/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Axiom audit

Usage (from the project root):

```bash
lake env lean --run scripts/check_axioms.lean Nivat.nivat_conjecture
```

Prints the axioms each named declaration depends on, and exits with code `1` if any of them
is outside the whitelist below.  Phase 0 of the blueprint is expected to *fail* this check on
`sorryAx`; the exit code is what makes the check usable in CI once the `sorry`s are gone.

Pass `--allow-sorry` to tolerate `sorryAx` (useful while the blueprint is still being filled in);
the three external results of §8.2 are always allowed, since the paper quotes them from the
literature.
-/
import Lean

open Lean

/-- Axioms that `Nivat.nivat_conjecture` is *allowed* to depend on: **only** the three axioms
of Lean's own logic.

Until 2026-09-18 this list also carried `Nivat.kari_szabados_prodShift`,
`Nivat.colle_doublyPeriodic` and `Nivat.colle_region`, the results §8.2 quoted from the
literature.  All three are now proved and their declarations are gone from the tree, so the
whitelist is back to the foundational three.  **Do not re-add a project axiom here**: an entry
in this list makes the gate green on an assumption, which is exactly the failure mode
`CLAUDE.md` 「进度用公理数衡量」 is guarding against. -/
def whitelist : List Name :=
  [`propext, `Classical.choice, `Quot.sound]

unsafe def main (args : List String) : IO UInt32 := do
  let allowSorry := args.contains "--allow-sorry"
  let names := (args.filter fun a => !a.startsWith "--").map String.toName
  if names.isEmpty then
    IO.eprintln "usage: lake env lean --run scripts/check_axioms.lean [--allow-sorry] DECL ..."
    return 1
  initSearchPath (← findSysroot)
  -- `Nivat.All`, not `Nivat`: the root imports only what the main theorem needs, which reaches
  -- one of the forty modules under `Nivat/External/Colle/`.  Importing the root would make this
  -- script silently blind to every declaration in the files the Colle work actually lives in.
  let env ← importModules #[{ module := `Nivat.All }] {}
  let ctx : Core.Context := { fileName := "check_axioms", fileMap := default }
  let mut bad := false
  for n in names do
    if !env.contains n then
      IO.eprintln s!"✗ {n}: no such declaration"
      bad := true
      continue
    let (axs, _) ← (Lean.collectAxioms n : CoreM (Array Name)).toIO ctx { env }
    if axs.isEmpty then
      IO.println s!"✓ {n}: depends on no axioms"
    else
      IO.println s!"  {n} depends on: {axs.toList}"
      for a in axs do
        if whitelist.contains a then
          continue
        if a == ``sorryAx && allowSorry then
          IO.println s!"  ! {n}: uses sorryAx (tolerated by --allow-sorry)"
          continue
        IO.eprintln s!"✗ {n}: non-whitelisted axiom {a}"
        bad := true
  return if bad then 1 else 0

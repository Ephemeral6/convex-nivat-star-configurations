"""Appendix C.2, Experiment 1: random star configurations with non-trivial
tangential periods, periodic tails and arbitrary transition strips.

Usage:  python verify.py [N] [seed]        (defaults N = 84, seed = 1)
"""

import sys

import numpy as np

import star as st

N = int(sys.argv[1]) if len(sys.argv) > 1 else 84
SEED = int(sys.argv[2]) if len(sys.argv) > 2 else 1
rng = np.random.default_rng(SEED)

DIRS = [(1, 0), (0, 1), (1, 1), (1, -1), (1, 2), (2, 1), (1, -2), (2, -1)]

WINDOWS = [
    ("2x3", st.window_from_vertices([(0, 0), (1, 0), (0, 2), (1, 2)])),
    ("3x3", st.window_from_vertices([(0, 0), (2, 0), (0, 2), (2, 2)])),
    ("2x4", st.window_from_vertices([(0, 0), (1, 0), (0, 3), (1, 3)])),
    ("4x2", st.window_from_vertices([(0, 0), (3, 0), (0, 1), (3, 1)])),
    ("triangle", st.window_from_vertices([(0, 0), (2, 0), (0, 2)])),
    ("hexagon", st.window_from_vertices([(1, 0), (2, 0), (3, 1), (2, 2), (1, 2), (0, 1)])),
    ("rhombus", st.window_from_vertices([(0, 0), (1, 1), (2, 0), (1, -1)])),
    ("segment", st.window_from_vertices([(0, 0), (2, 0)])),
]


def random_component(p, v, equal_tails):
    """Random component in direction v.  With equal_tails the left and right
    tails coincide (as a table), which is what makes Case B reachable."""
    while True:
        k = int(rng.integers(1, 4))            # tangential period 1..3
        aL = int(rng.integers(1, 3))           # tail periods 1..2 rows
        aR = aL if equal_tails else int(rng.integers(1, 3))
        width = int(rng.integers(1, 4))        # strip width 1..3
        ell = int(rng.integers(-1, 2))
        strip = rng.integers(0, p, size=(width, k))
        Ltab = rng.integers(0, p, size=(aL, k))
        Rtab = Ltab if equal_tails else rng.integers(0, p, size=(aR, k))
        c = st.Component(v, k, ell, ell + width - 1, strip, Ltab, Rtab)
        if c.is_nondegenerate():
            return c


def random_star():
    p = int(rng.choice([2, 3, 5]))
    m = int(rng.choice([2, 3]))
    idx = rng.choice(len(DIRS), size=m, replace=False)
    # component 1 may have different left and right tails; the others do not
    return st.Star(p, [random_component(p, DIRS[i], j > 0) for j, i in enumerate(idx)])


for name, S in WINDOWS:
    assert st.is_lattice_convex(S)
print("windows:", ", ".join(f"{name} ({len(S)} pts)" for name, S in WINDOWS))
print(f"seed = {SEED}, N = {N}")

tally = {"A": 0, "B": 0}
results = []
for n in range(N):
    star = random_star()
    res = st.analyse(star, WINDOWS, rng)
    res["ok"] = st.config_ok(res)
    results.append(res)
    tally[res["case"]] += 1
    line = (f"[{n:3d}] p={res['p']} m={res['m']} dirs={res['dirs']} "
            f"kappa={res['kappa']} case={res['case']} d={res['d']} "
            f"P={[r['P'] for r in res['windows']]} "
            f"|S|+1={[r['size'] + 1 for r in res['windows']]} ok={res['ok']}")
    if res["case"] == "B":
        line += (f" | RZ={[len(r['RZ']) for r in res['windows']]}"
                 f" dimU={[r['dimU'] for r in res['windows']]}"
                 f" witnesses={len(res['witnesses'])}"
                 f" Ae_err={res['Ae_periodicity_error']:.1e}")
    print(line, flush=True)

caseB = [res for res in results if res["case"] == "B"]
failures = [res for res in results if not res["ok"]]
print()
print(f"Case A: {tally['A']}   Case B: {tally['B']}   failures: {len(failures)}")
print("Theorem T (P >= |S|+1) on every window of every configuration:",
      all(r["theoremT"] for res in results for r in res["windows"]))
print("pattern counts unchanged when the box radius is doubled (90 -> 180):",
      all(r["P"] == r["P_doubled"] for res in results for r in res["windows"]))
if caseB:
    print("Case B: values of d_i observed:",
          sorted(set(d for res in caseB for d in res["d"])))
    print("Case B: windows with R_Z(S) non-empty:",
          sum(1 for res in caseB for r in res["windows"] if r["RZ"]))
    print("Case B: max |A e_theta| periodicity error:",
          max(res["Ae_periodicity_error"] for res in caseB))
    print("Case B: every configuration has a witness d:",
          all(res["witnesses"] for res in caseB))
    print("Case B: Lemma 4.2 (dim U_S >= |S|+1-|R_Z(S)|) on every window:",
          all(r["budget"] for res in caseB for r in res["windows"]))
for res in failures:
    print("FAILURE:", res)

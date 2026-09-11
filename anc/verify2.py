"""Appendix C.2, Experiment 2: configurations of the form sum_i w_i o pi_i,
i.e. k_i = 1 and constant tails, aimed at Case B with R_Z(S) non-empty.

Each w_i : Z -> F_p takes a constant value c_i outside a window of length 1..4
and arbitrary values inside it (not all equal to c_i, so (S2) holds).

Usage:  python verify2.py [N] [seed]        (defaults N = 157, seed = 7)
"""

import sys

import numpy as np

import star as st

N = int(sys.argv[1]) if len(sys.argv) > 1 else 157
SEED = int(sys.argv[2]) if len(sys.argv) > 2 else 7
rng = np.random.default_rng(SEED)

DIRS = [(1, 0), (0, 1), (1, 1), (1, -1), (1, 2), (2, 1), (1, -2), (2, -1),
        (1, 3), (3, 1), (1, -3)]

WINDOWS = [
    ("3x4", st.window_from_vertices([(0, 0), (2, 0), (0, 3), (2, 3)])),
    ("4x4", st.window_from_vertices([(0, 0), (3, 0), (0, 3), (3, 3)])),
    ("5x3", st.window_from_vertices([(0, 0), (4, 0), (0, 2), (4, 2)])),
    ("4x3", st.window_from_vertices([(0, 0), (3, 0), (0, 2), (3, 2)])),
    ("triangle", st.window_from_vertices([(0, 0), (4, 0), (0, 4)])),
    ("hexagon", st.window_from_vertices([(1, 0), (3, 0), (4, 2), (3, 4), (1, 4), (0, 2)])),
    ("rhombus", st.window_from_vertices([(0, 0), (2, 2), (4, 0), (2, -2)])),
    ("parallelogram", st.window_from_vertices([(0, 0), (3, 0), (5, 2), (2, 2)])),
]


def random_component(p, v):
    while True:
        c = int(rng.integers(0, p))
        width = int(rng.integers(1, 5))
        ell = int(rng.integers(-2, 3))
        strip = rng.integers(0, p, size=(width, 1))
        comp = st.Component(v, 1, ell, ell + width - 1, strip, [[c]], [[c]])
        if comp.is_nondegenerate():
            return comp


def random_star():
    p = int(rng.choice([2, 3, 5]))
    m = int(rng.choice([2, 3], p=[0.7, 0.3]))
    idx = rng.choice(len(DIRS), size=m, replace=False)
    return st.Star(p, [random_component(p, DIRS[i]) for i in idx])


def supports_meet(star, G=30):
    """Observation C.1: do the deviation fields delta_1, delta_2 have a
    common support point?"""
    xs = np.arange(-G, G + 1, dtype=np.int64)
    X, Y = np.meshgrid(xs, xs, indexing="ij")
    c1, c2 = star.comps
    d1 = c1.F(X, Y) != c1.Ltilde(X, Y)
    d2 = c2.F(X, Y) != c2.Ltilde(X, Y)
    return bool(np.any(d1 & d2))


for name, S in WINDOWS:
    assert st.is_lattice_convex(S)
print("windows:", ", ".join(f"{name} ({len(S)} pts)" for name, S in WINDOWS))
print(f"seed = {SEED}, N = {N}")

tally = {"A": 0, "B": 0}
results = []
obs_agree = obs_total = 0
for n in range(N):
    star = random_star()
    res = st.analyse(star, WINDOWS, rng)
    res["ok"] = st.config_ok(res)
    results.append(res)
    tally[res["case"]] += 1
    if star.m == 2:
        obs_total += 1
        predicted = "A" if supports_meet(star) else "B"
        obs_agree += predicted == res["case"]
        res["det"] = st.det2(star.comps[0].v, star.comps[1].v)
    line = (f"[{n:3d}] p={res['p']} m={res['m']} dirs={res['dirs']} "
            f"case={res['case']} d={res['d']} "
            f"P={[r['P'] for r in res['windows']]} ok={res['ok']}")
    if res["case"] == "B":
        line += (f" | RZ={[len(r['RZ']) for r in res['windows']]}"
                 f" dimU={[r['dimU'] for r in res['windows']]}"
                 f" H2={[r.get('H2') for r in res['windows']]}"
                 f" witness={res.get('witness')} Ae_err={res['Ae_periodicity_error']:.1e}")
    print(line, flush=True)

caseB = [res for res in results if res["case"] == "B"]
failures = [res for res in results if not res["ok"]]
print()
print(f"Case A: {tally['A']}   Case B: {tally['B']}   failures: {len(failures)}")
print("Theorem T (P >= |S|+1) on every window of every configuration:",
      all(r["theoremT"] for res in results for r in res["windows"]))
print("pattern counts unchanged when the box radius is doubled (90 -> 180):",
      all(r["P"] == r["P_doubled"] for res in results for r in res["windows"]))
print(f"Observation C.1 (m = 2): prediction agrees with the computed case on "
      f"{obs_agree} of {obs_total} two-component configurations")
print("Case B with m = 2: values of |det(v_1, v_2)| observed:",
      sorted(set(abs(res["det"]) for res in caseB if res["m"] == 2)))
withRZ = [(res, r) for res in caseB for r in res["windows"] if r["RZ"]]
print(f"Case B configurations: {len(caseB)}, of which "
      f"{sum(1 for res in caseB if any(r['RZ'] for r in res['windows']))} have some "
      f"window with R_Z(S) non-empty; Case-B (configuration, window) pairs with "
      f"R_Z(S) non-empty: {len(withRZ)}")
print("  |R_Z(S)| values:", sorted(set(len(r["RZ"]) for _, r in withRZ)))
print("  m values among them:", sorted(set(res["m"] for res, _ in withRZ)))
print("  d_i values among them:", sorted(set(d for res, _ in withRZ for d in res["d"])))
print("  dim U_S == |S|+1-|R_Z(S)| exactly on all of them:",
      all(r["dimU"] == r["size"] + 1 - len(r["RZ"]) for _, r in withRZ))
print("  H_2(S) == dim U_S + |R_Z(S)| (Lemma 7.2) on all of them:",
      all(r["independent"] for _, r in withRZ))
print("  H_2(S) >= |S|+1 on all of them:", all(r["H2_ok"] for _, r in withRZ))
if caseB:
    print("Case B: max |A e_theta| periodicity error:",
          max(res["Ae_periodicity_error"] for res in caseB))
    print("Case B: every configuration has a witness d:",
          all(res["witnesses"] for res in caseB))
    print("Case B: Lemma 4.2 (dim U_S >= |S|+1-|R_Z(S)|) on every window:",
          all(r["budget"] for res in caseB for r in res["windows"]))

print()
print("Table: p | directions | S | |S| | P | d_i | |R_Z| | dim U_S | |S|+1-|R_Z| | H_2 | witness d")
for res, r in withRZ:
    print(f"  {res['p']} | {res['dirs']} | {r['window']} | {r['size']} | {r['P']} | "
          f"{tuple(res['d'])} | {len(r['RZ'])} | {r['dimU']} | "
          f"{r['size'] + 1 - len(r['RZ'])} | {r['H2']} | {res['witness']}")
for res in failures:
    print("FAILURE:", res)

"""Appendix C.3: the counterexample showing that Lemma 3.1 fails for
non-realised tail choices.

p = 2, m = 3, v_1 = (1,0), v_2 = (0,-1), v_3 = (1,-1);
L_1 = 0, R_1 = 1[x even]; L_2 = L_3 = 0, R_2 = R_3 = 1[3 | x];
every transition strip is the single row pi_i = 0 with constant value 1.
"""

import numpy as np

import star as st


def tables(v, k, a, f):
    """Tail table [t mod a, s mod k] of the doubly periodic field f(x, y),
    which must have periods k v and a u."""
    u = st.dual_basis(v)
    tab = np.zeros((a, k), dtype=np.int64)
    for t in range(a):
        for s in range(k):
            tab[t, s] = f(s * v[0] + t * u[0], s * v[1] + t * u[1])
    # consistency: f really has the claimed periods
    for t in range(-6, 7):
        for s in range(-6, 7):
            x, y = s * v[0] + t * u[0], s * v[1] + t * u[1]
            assert f(x, y) == tab[t % a, s % k], "tail not periodic as claimed"
    return tab


zero = lambda x, y: 0
even_x = lambda x, y: 1 if x % 2 == 0 else 0
three_x = lambda x, y: 1 if x % 3 == 0 else 0

v1, v2, v3 = (1, 0), (0, -1), (1, -1)
c1 = st.Component(v1, 2, 0, 0, [[1, 1]], tables(v1, 2, 1, zero), tables(v1, 2, 1, even_x))
c2 = st.Component(v2, 1, 0, 0, [[1]], tables(v2, 1, 3, zero), tables(v2, 1, 3, three_x))
c3 = st.Component(v3, 3, 0, 0, [[1, 1, 1]], tables(v3, 3, 3, zero), tables(v3, 3, 3, three_x))
S = st.Star(2, [c1, c2, c3])

print("p =", S.p, " m =", S.m, " kappa =", S.kappa, " H =", S.H)
print("pi_2(v_1) =", st.det2(v2, v1), " pi_3(v_1) =", st.det2(v3, v1))

# --- Lambda_1 ---------------------------------------------------------------
freqs, kap = st.spectrum(S, 0)
roots = st.roots_of(freqs, kap)
print("kappa_1 =", kap, " frequencies =", freqs,
      " Lambda_1 =", [complex(round(r.real, 12), round(r.imag, 12)) for r in roots])
A1 = np.poly(roots)
print("A_1(t) coefficients (highest degree first) =", np.round(A1, 12))

# A_1(T^{v_1}) as a Laurent polynomial in T
A1T = {}
for jj, cf in enumerate(A1):
    e = len(roots) - jj
    A1T[(e * v1[0], e * v1[1])] = cf
A1T = {k: c for k, c in A1T.items() if abs(c) > 1e-12}
print("A_1(T^{v_1}) =", {k: complex(round(c.real, 12), round(c.imag, 12)) for k, c in A1T.items()})

# --- the grids -------------------------------------------------------------
G, box = 40, 20
xs = np.arange(-G, G + 1, dtype=np.int64)
X, Y = np.meshgrid(xs, xs, indexing="ij")
L1, R1 = c1.Ltilde(X, Y), c1.Rtilde(X, Y)
L2, R2 = c2.Ltilde(X, Y), c2.Rtilde(X, Y)
L3, R3 = c3.Ltilde(X, Y), c3.Rtilde(X, Y)


def difference(B, a):
    """1[R_1 + B = a] - 1[L_1 + B = a], as a float grid."""
    return ((np.mod(R1 + B, 2) == a).astype(float)
            - (np.mod(L1 + B, 2) == a).astype(float))


# realised sectors: sigma = +1 gives (R_2, R_3), sigma = -1 gives (L_2, L_3)
for name, B in (("(R_2,R_3)", R2 + R3), ("(L_2,L_3)", L2 + L3)):
    for a in (0, 1):
        val = np.max(np.abs(st.apply_laurent(A1T, difference(B, a), G, box)))
        print(f"realised background {name}, colour {a}: "
              f"max |A_1(T^{{v_1}}) (e_R - e_L)| = {val:.3e}")

# the non-realised mixed choice (R_1, R_2, L_3) versus (L_1, R_2, L_3)
B = R2 + L3
for a in (0, 1):
    D1 = difference(B, a)
    val = np.max(np.abs(st.apply_laurent(A1T, D1, G, box)))
    print(f"mixed background (R_2,L_3), colour {a}: "
          f"max |A_1(T^{{v_1}}) Delta_1| = {val:.3e}")
    if a == 1:
        row = [int(D1[x + G, 0 + G]) for x in range(0, 6)]
        row2 = [int(D1[x + 2 + G, 0 + G]) for x in range(0, 6)]
        print("  Delta_1(x, 0) for x = 0..5:          ", row)
        print("  Delta_1(x + 2, 0) for x = 0..5:      ", row2)
        print("  (T^{2 v_1} - 1) Delta_1 at x = 0..5: ", [b - a_ for a_, b in zip(row, row2)])

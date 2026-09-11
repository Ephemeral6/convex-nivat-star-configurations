"""Machinery for the numerical verification of the convex Nivat paper.

Objects and conventions follow Sections 0-7 of the paper.

A star configuration is a sum theta = sum_i F_i over F_p.  Component i is given
by a primitive direction v_i, a tangential period k_i, a transition strip
[ell_i, r_i] carrying an arbitrary value table, and left/right tails L_i, R_i
given as doubly periodic tables.  Everything is expressed in the integral basis
(v_i, u_i) with det(v_i, u_i) = 1, in which

    z = s v_i + t u_i,   t = pi_i(z) = det(v_i, z),   s = det(z, u_i).

A tail table is indexed [t mod a, s mod k]; the strip table is indexed
[t - ell, s mod k].  Such a component automatically satisfies (S1) and (S3);
(S2) is checked exactly by Component.is_nondegenerate.

No external dependency beyond numpy.
"""

import itertools
from math import gcd

import numpy as np

Q = 2147483647  # 2^31 - 1, prime; ranks are computed over F_Q


# --------------------------------------------------------------------------
# integer helpers
# --------------------------------------------------------------------------

def lcm(a, b):
    return abs(a * b) // gcd(a, b) if a and b else 0


def lcm_all(xs):
    out = 1
    for x in xs:
        out = lcm(out, x)
    return out


def egcd(a, b):
    """Return (g, x, y) with a*x + b*y = g = gcd(a, b) >= 0."""
    old_r, r = a, b
    old_x, x = 1, 0
    old_y, y = 0, 1
    while r:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_x, x = x, old_x - q * x
        old_y, y = y, old_y - q * y
    if old_r < 0:
        old_r, old_x, old_y = -old_r, -old_x, -old_y
    return old_r, old_x, old_y


def det2(a, b):
    return a[0] * b[1] - a[1] * b[0]


def dual_basis(v):
    """u with det(v, u) = 1; requires v primitive."""
    g, x, y = egcd(v[0], v[1])
    assert g == 1, "direction must be primitive"
    # want v0*u1 - v1*u0 = 1, so u = (-y, x)
    u = (-y, x)
    assert det2(v, u) == 1
    return u


# --------------------------------------------------------------------------
# plane geometry on the lattice
# --------------------------------------------------------------------------

def convex_hull(pts):
    """Counter-clockwise hull of integer points.  Collinear input returns the
    two extreme points."""
    pts = sorted(set(tuple(map(int, p)) for p in pts))
    if len(pts) <= 2:
        return pts

    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

    lower = []
    for p in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    upper = []
    for p in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    hull = lower[:-1] + upper[:-1]
    if len(hull) < 3:
        return [pts[0], pts[-1]]
    return hull


def in_hull(hull, p):
    """Is the integer point p in the convex hull (boundary included)?"""
    if len(hull) == 1:
        return tuple(p) == hull[0]
    if len(hull) == 2:
        a, b = hull
        if (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0]) != 0:
            return False
        return (min(a[0], b[0]) <= p[0] <= max(a[0], b[0])
                and min(a[1], b[1]) <= p[1] <= max(a[1], b[1]))
    n = len(hull)
    for i in range(n):
        a, b = hull[i], hull[(i + 1) % n]
        if (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0]) < 0:
            return False
    return True


def lattice_points(hull):
    xs = [h[0] for h in hull]
    ys = [h[1] for h in hull]
    out = []
    for x in range(min(xs), max(xs) + 1):
        for y in range(min(ys), max(ys) + 1):
            if in_hull(hull, (x, y)):
                out.append((x, y))
    return out


def window_from_vertices(verts):
    """The lattice-convex window Conv(verts) cap Z^2."""
    return sorted(lattice_points(convex_hull(verts)))


def is_lattice_convex(S):
    return sorted(map(tuple, S)) == sorted(lattice_points(convex_hull(S)))


def zonotope_vertices(dirs):
    """Subset sums of the generators; a superset of the vertices of
    sum_i [0, d_i v_i], which is all the hull routine needs."""
    pts = [(0, 0)]
    for g in dirs:
        pts = [(p[0] + c * g[0], p[1] + c * g[1]) for p in pts for c in (0, 1)]
    return pts


def R_Z(S, gens):
    """{ r in Z^2 : r + Z subset Conv(S) }, Z = sum_i [0, gens_i]."""
    hullS = convex_hull(S)
    if len(hullS) < 3:
        return []          # Z is two-dimensional, Conv(S) is not
    zv = zonotope_vertices(gens)
    xs = [h[0] for h in hullS]
    ys = [h[1] for h in hullS]
    zx = [q[0] for q in zv]
    zy = [q[1] for q in zv]
    out = []
    for rx in range(min(xs) - max(zx), max(xs) - min(zx) + 1):
        for ry in range(min(ys) - max(zy), max(ys) - min(zy) + 1):
            if all(in_hull(hullS, (rx + q[0], ry + q[1])) for q in zv):
                out.append((rx, ry))
    return out


def minkowski_difference_points(gens):
    """(Z - Z) cap Z^2 for Z = sum_i [0, gens_i]."""
    zv = zonotope_vertices(gens)
    diff = [(a[0] - b[0], a[1] - b[1]) for a in zv for b in zv]
    return lattice_points(convex_hull(diff))


# --------------------------------------------------------------------------
# linear algebra over F_Q
# --------------------------------------------------------------------------

def rank_mod(rows, q=Q):
    M = [[int(x) % q for x in row] for row in rows]
    if not M:
        return 0
    nr, nc = len(M), len(M[0])
    r = 0
    for c in range(nc):
        piv = None
        for i in range(r, nr):
            if M[i][c]:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], q - 2, q)
        M[r] = [(x * inv) % q for x in M[r]]
        for i in range(nr):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(M[i][j] - f * M[r][j]) % q for j in range(nc)]
        r += 1
        if r == nr:
            break
    return r


# --------------------------------------------------------------------------
# components and star configurations
# --------------------------------------------------------------------------

class Component:
    def __init__(self, v, k, ell, r, strip, Ltab, Rtab):
        self.v = (int(v[0]), int(v[1]))
        assert gcd(abs(self.v[0]), abs(self.v[1])) == 1, "v must be primitive"
        self.u = dual_basis(self.v)
        self.k = int(k)
        self.ell = int(ell)
        self.r = int(r)
        assert self.ell <= self.r + 1
        self.strip = np.asarray(strip, dtype=np.int64)     # (r-ell+1, k)
        self.Ltab = np.asarray(Ltab, dtype=np.int64)       # (aL, k)
        self.Rtab = np.asarray(Rtab, dtype=np.int64)       # (aR, k)
        assert self.strip.shape == (self.r - self.ell + 1, self.k)
        assert self.Ltab.shape[1] == self.k and self.Rtab.shape[1] == self.k
        self.aL = self.Ltab.shape[0]
        self.aR = self.Rtab.shape[0]

    # --- coordinates -------------------------------------------------------
    def st(self, z1, z2):
        t = self.v[0] * z2 - self.v[1] * z1
        s = z1 * self.u[1] - z2 * self.u[0]
        return s, t

    # --- fields ------------------------------------------------------------
    def Ltilde(self, z1, z2):
        s, t = self.st(z1, z2)
        return self.Ltab[np.mod(t, self.aL), np.mod(s, self.k)]

    def Rtilde(self, z1, z2):
        s, t = self.st(z1, z2)
        return self.Rtab[np.mod(t, self.aR), np.mod(s, self.k)]

    def F(self, z1, z2):
        s, t = self.st(z1, z2)
        sm = np.mod(s, self.k)
        L = self.Ltab[np.mod(t, self.aL), sm]
        R = self.Rtab[np.mod(t, self.aR), sm]
        idx = np.clip(t - self.ell, 0, self.strip.shape[0] - 1)
        St = self.strip[idx, sm]
        return np.where(t < self.ell, L, np.where(t > self.r, R, St))

    # --- axiom (S2) --------------------------------------------------------
    def is_nondegenerate(self):
        """F_i is doubly periodic iff it equals the global extension of its
        left tail (a doubly periodic function vanishing on a half-plane
        vanishes identically).  So (S2) holds iff F_i differs from Ltilde
        somewhere, and that can be decided on finitely many rows."""
        for t in range(self.ell, self.r + 1):
            for s in range(self.k):
                if self.strip[t - self.ell, s] != self.Ltab[t % self.aL, s]:
                    return True
        per = lcm(self.aL, self.aR)
        for t in range(self.r + 1, self.r + 1 + per):
            for s in range(self.k):
                if self.Rtab[t % self.aR, s] != self.Ltab[t % self.aL, s]:
                    return True
        return False


class Star:
    def __init__(self, p, comps):
        self.p = int(p)
        self.comps = list(comps)
        self.m = len(comps)
        assert self.m >= 2
        for i in range(self.m):
            for j in range(i + 1, self.m):
                assert det2(comps[i].v, comps[j].v) != 0, "directions parallel"
        for c in comps:
            assert c.is_nondegenerate(), "component violates (S2)"
        # Gamma contains M Z^2 with M the lcm below, so kappa_i = M k_i works.
        self.M = lcm_all([lcm_all([c.k, c.aL, c.aR]) for c in comps])
        self.kappa = [self.M * c.k for c in comps]
        self.H = [(self.kappa[i] * comps[i].v[0], self.kappa[i] * comps[i].v[1])
                  for i in range(self.m)]

    # --- the configuration -------------------------------------------------
    def theta(self, z1, z2):
        out = np.zeros(np.shape(z1), dtype=np.int64)
        for c in self.comps:
            out = out + c.F(z1, z2)
        return np.mod(out, self.p)

    def grid(self, G):
        xs = np.arange(-G, G + 1, dtype=np.int64)
        X, Y = np.meshgrid(xs, xs, indexing="ij")
        return self.theta(X, Y)

    # --- the difference operator ------------------------------------------
    def subset_shifts(self):
        """[(H_C, sign)] over all C subset [m], sign = (-1)^(m-|C|)."""
        out = []
        for mask in range(1 << self.m):
            hx = hy = 0
            bits = 0
            for i in range(self.m):
                if mask >> i & 1:
                    hx += self.H[i][0]
                    hy += self.H[i][1]
                    bits += 1
            out.append(((hx, hy), (-1) ** (self.m - bits)))
        return out

    def maxH(self):
        sh = self.subset_shifts()
        return max(max(abs(h[0]), abs(h[1])) for h, _ in sh)


def sub(arr, G, box, u=(0, 0)):
    """The block { z + u : |z|_inf <= box } of an array indexed by z + (G,G)."""
    a = -box + u[0] + G
    b = -box + u[1] + G
    return arr[a:a + 2 * box + 1, b:b + 2 * box + 1]


# --------------------------------------------------------------------------
# Case A / Case B
# --------------------------------------------------------------------------

def apply_D(vals, star, G, box):
    """(D f) on the box, for f given on the grid of radius G."""
    out = np.zeros((2 * box + 1, 2 * box + 1), dtype=vals.dtype)
    for h, sgn in star.subset_shifts():
        out = out + sgn * sub(vals, G, box, h)
    return out


def case_of(star, G, box):
    """'A' if D 1[theta = a] is non-zero for some colour a, else 'B'."""
    th = star.grid(G)
    for a in range(star.p):
        Ia = (th == a).astype(np.int64)
        if np.any(apply_D(Ia, star, G, box) != 0):
            return "A"
    return "B"


# --------------------------------------------------------------------------
# exceptional spectra
# --------------------------------------------------------------------------

def tail_choice_sign(star, i, j, sigma):
    """epsilon_j^sigma: True for the right tail R_j, False for L_j."""
    return sigma * det2(star.comps[j].v, star.comps[i].v) > 0


def _background(star, i, sigma, z1, z2):
    out = np.zeros(np.shape(z1), dtype=np.int64)
    for j, c in enumerate(star.comps):
        if j == i:
            continue
        out = out + (c.Rtilde(z1, z2) if tail_choice_sign(star, i, j, sigma)
                     else c.Ltilde(z1, z2))
    return out


def spectrum(star, i, tol=1e-9):
    """Lambda_i, as a sorted list of (numerator, kappa_i) frequency pairs and
    the corresponding roots of unity."""
    c = star.comps[i]
    kap = star.kappa[i]
    v, u = c.v, c.u
    lo = c.ell - 2 * star.M - 2
    hi = c.r + 2 * star.M + 2
    ks = np.arange(kap, dtype=np.int64)
    freqs = set()
    for t in range(lo, hi + 1):
        z1 = ks * v[0] + t * u[0]
        z2 = ks * v[1] + t * u[1]
        Xi = {}
        G = {}
        for sigma in (+1, -1):
            B = _background(star, i, sigma, z1, z2)
            Xi[sigma] = np.mod(c.F(z1, z2) + B, star.p)
            G[(sigma, "L")] = np.mod(c.Ltilde(z1, z2) + B, star.p)
            G[(sigma, "R")] = np.mod(c.Rtilde(z1, z2) + B, star.p)
        for sigma in (+1, -1):
            for eps in ("L", "R"):
                for a in range(star.p):
                    d = (Xi[sigma] == a).astype(float) - (G[(sigma, eps)] == a).astype(float)
                    if not np.any(d):
                        continue
                    F = np.fft.fft(d) / kap
                    for jj in np.nonzero(np.abs(F) > tol)[0]:
                        freqs.add(int(jj))
    return sorted(freqs), kap


def roots_of(freqs, kap):
    return [np.exp(2j * np.pi * f / kap) for f in freqs]


def laurent_of_A(star, spectra):
    """A(T) = prod_i A_i(T^{v_i}) as a dict {(a,b): complex}, together with the
    generators d_i v_i of the zonotope Z."""
    A = {(0, 0): 1.0 + 0j}
    gens = []
    for i, (freqs, kap) in enumerate(spectra):
        roots = roots_of(freqs, kap)
        coeffs = np.poly(roots) if roots else np.array([1.0 + 0j])
        di = len(roots)
        v = star.comps[i].v
        Ai = {}
        for jj, cf in enumerate(coeffs):          # cf is the coefficient of t^(di-jj)
            e = di - jj
            Ai[(e * v[0], e * v[1])] = Ai.get((e * v[0], e * v[1]), 0) + cf
        newA = {}
        for k1, c1 in A.items():
            for k2, c2 in Ai.items():
                key = (k1[0] + k2[0], k1[1] + k2[1])
                newA[key] = newA.get(key, 0) + c1 * c2
        A = {k: c for k, c in newA.items() if abs(c) > 1e-12}
        gens.append((di * v[0], di * v[1]))
    return A, gens


def apply_laurent(poly, vals, G, box):
    out = np.zeros((2 * box + 1, 2 * box + 1), dtype=complex)
    for u, c in poly.items():
        out = out + c * sub(vals, G, box, u)
    return out


# --------------------------------------------------------------------------
# patterns, ranks, witnesses: the full check of one configuration
# --------------------------------------------------------------------------

def patterns(th, G, S, R):
    """Distinct S-patterns of theta at anchors |u|_inf <= R (rows of an array)."""
    cols = [sub(th, G, R, s).reshape(-1) for s in S]
    return np.unique(np.stack(cols, axis=1), axis=0)


def analyse(star, windows, rng, R=90, R2=180, box=40):
    """Run every check of Appendix C on one star configuration.

    Returns a dict with the case, the spectra, and one record per window.  In
    Case B the record also carries dim U_S, |R_Z(S)|, the witness d, and the
    rank H_2(S) of the combined linear/quadratic system."""
    m, p = star.m, star.p
    maxs = max(max(abs(s[0]), abs(s[1])) for _, S in windows for s in S)
    maxH = star.maxH()
    G = max(R2 + maxs, box + 2 * maxH + star.M + 2)
    th = star.grid(G)
    out = {"p": p, "m": m, "dirs": [c.v for c in star.comps],
           "kappa": list(star.kappa), "G": G}

    # ---- Case A / Case B --------------------------------------------------
    caseB = True
    for a in range(p):
        if np.any(apply_D((th == a).astype(np.int64), star, G, box) != 0):
            caseB = False
            break
    out["case"] = "B" if caseB else "A"

    # ---- spectra, A, Z ----------------------------------------------------
    spectra = [spectrum(star, i) for i in range(m)]
    A, gens = laurent_of_A(star, spectra)
    out["freqs"] = [f for f, _ in spectra]
    out["d"] = [len(f) for f, _ in spectra]
    out["gens"] = gens

    # ---- encoding ---------------------------------------------------------
    w = rng.choice(np.arange(1, 101), size=p, replace=False).astype(np.int64)
    eta = w[th]
    out["w"] = w.tolist()

    # ---- Proposition 3.3: A e_theta is doubly periodic (Case B only) ------
    if caseB:
        dev = 0.0
        for a in range(p):
            Ae = apply_laurent(A, (th == a).astype(float), G, box + star.M)
            inner = Ae[star.M:2 * box + 1 + star.M, star.M:2 * box + 1 + star.M]
            for sh in ((star.M, 0), (0, star.M)):
                shifted = Ae[star.M + sh[0]:2 * box + 1 + star.M + sh[0],
                             star.M + sh[1]:2 * box + 1 + star.M + sh[1]]
                dev = max(dev, float(np.max(np.abs(shifted - inner))))
        out["Ae_periodicity_error"] = dev

        # ---- Proposition 5.3: a witness d in (Z - Z) with J(d, .) != 0 ----
        Zpts = lattice_points(convex_hull(zonotope_vertices(gens)))
        witnesses = []
        for d in minkowski_difference_points(gens):
            if d == (0, 0):
                continue
            # h(z) = eta(z) eta(z + d) on the grid of radius G - |d|
            Gd = G - max(abs(d[0]), abs(d[1]))
            h = sub(eta, G, Gd) * sub(eta, G, Gd, d)
            J = apply_D(h, star, Gd, box)
            if np.any(J != 0):
                witnesses.append(d)
        out["witnesses"] = witnesses
        if witnesses:
            d = witnesses[0]
            Zset = set(Zpts)
            q = next(q for q in Zpts if (q[0] + d[0], q[1] + d[1]) in Zset)
            out["witness"] = d
            out["q"] = q

    # ---- per window -------------------------------------------------------
    recs = []
    for name, S in windows:
        rec = {"window": name, "size": len(S)}
        pats = patterns(th, G, S, R)
        pats2 = patterns(th, G, S, R2)
        rec["P"] = int(pats.shape[0])
        rec["P_doubled"] = int(pats2.shape[0])
        rec["RZ"] = R_Z(S, gens)
        rec["theoremT"] = rec["P"] >= len(S) + 1
        if caseB:
            lin = [[1] + [int(w[c]) for c in row] for row in pats]
            rec["dimU"] = rank_mod(lin)
            rec["budget"] = rec["dimU"] >= len(S) + 1 - len(rec["RZ"])
            if rec["RZ"] and witnesses:
                idx = {s: j for j, s in enumerate(S)}
                quad = []
                for r in rec["RZ"]:
                    a = (r[0] + q[0], r[1] + q[1])
                    b = (a[0] + d[0], a[1] + d[1])
                    assert a in idx and b in idx, "Lemma 6.1 violated"
                    quad.append((idx[a], idx[b]))
                full = [row + [int(w[pats[k, ia]]) * int(w[pats[k, ib]]) for ia, ib in quad]
                        for k, row in enumerate(lin)]
                rec["H2"] = rank_mod(full)
                rec["independent"] = rec["H2"] == rec["dimU"] + len(rec["RZ"])
                rec["H2_ok"] = rec["H2"] >= len(S) + 1
        recs.append(rec)
    out["windows"] = recs
    return out


def config_ok(res):
    """All checks of the paper pass on this configuration?"""
    ok = all(r["theoremT"] and r["P"] == r["P_doubled"] for r in res["windows"])
    if res["case"] == "B":
        ok = ok and res["Ae_periodicity_error"] < 1e-8
        ok = ok and bool(res["witnesses"])
        for r in res["windows"]:
            ok = ok and r["budget"]
            if r["RZ"]:
                ok = ok and r["independent"] and r["H2_ok"]
    return ok

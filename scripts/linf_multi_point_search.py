"""Filling areas of the n-point Kuratowski boundary curve in the sup-norm space L^inf_n.

For anchors theta_1..theta_n on the circle of length 2 pi, the boundary curve is

    gamma_n(theta) = (d(theta, theta_1), ..., d(theta, theta_n))  in  (R^n, sup norm).

Each coordinate is piecewise linear with breaks at theta_i and theta_i + pi, so gamma_n is
exactly a closed polygon. For an isometric filling M, the map
q_n(x) = (d(x, b_1), ..., d(x, b_n)) is 1-Lipschitz into L^inf_n and sends dM onto gamma_n,
so mu_H^2(M) >= mu_H^2(q_n(M)). Two kinds of numbers come out of that:

* LOWER bounds (provable): 1-Lipschitz maps from L^inf_n to a normed plane and the covering
  argument. For linear maps into the sup-norm plane the best is the best anchor pair,
  2 phi (pi - phi) at separation phi, and this is at most pi^2/2 for every n.
* UPPER bounds (numerical): explicit surfaces spanning gamma_n in L^inf_n. They bound the
  minimal filling area of gamma_n from above, which is the CEILING of any argument that goes
  through q_n. They are not lower bounds on Area(M).

Area unit: Mathlib's unnormalized 2-dimensional Hausdorff measure mu_H^2. On a sup-norm plane
it is Lebesgue measure; on a Riemannian surface it is (4/pi) x area, so the round hemisphere
has mu_H^2 = 8. On a 2-plane P in L^inf_n, mu_H^2 = 4 lambda / lambda(B_P), with
B_P = P cap unit cube. For a flat triangle P0 + {s u + t v : s, t >= 0, s + t <= 1} this gives

    mu_H^2(triangle) = 2 / area{(s, t) : |s u_i + t v_i| <= 1 for all i},

which is computed exactly from the convex hull of +-(u_i, v_i). The gradient is analytic: if
the facet {w . x = 1} of that polygon has edge E, then d area / d w = -(|E| / |w|) mid(E).

Upper-bound surfaces: (1) the cone from an optimized apex; (2) a triangulated disk with R
rings and M boundary points (boundary vertices exactly on gamma_n, interior free in R^n),
minimizing the total mu_H^2 by L-BFGS-B with the analytic gradient, started from the cone and
from the Kuratowski image of a round hemisphere; (3) the PL image of the round hemisphere
itself (its exact mu_H^2 is at most 8).

Usage:  .venv/bin/python3 scripts/linf_multi_point_search.py
        .venv/bin/python3 scripts/linf_multi_point_search.py --check-grad
"""

from __future__ import annotations

import argparse
import json
import os
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

TWO_PI = 2.0 * np.pi
PI_SQ_2 = np.pi**2 / 2
HEMISPHERE_MUH = 8.0  # (4 / pi) * 2 pi


def circ_dist(a, b):
    d = np.abs(np.asarray(a) - np.asarray(b)) % TWO_PI
    return np.minimum(d, TWO_PI - d)


def boundary_breaks(anchors: np.ndarray) -> np.ndarray:
    """Sorted break angles of gamma_n: every theta_i and theta_i + pi (mod 2 pi)."""
    br = np.concatenate([anchors % TWO_PI, (anchors + np.pi) % TWO_PI])
    br = np.unique(np.round(br, 12))
    return br


def pair_lower_bound(anchors: np.ndarray) -> float:
    """Best linear sup-plane projection bound: max over anchor pairs of 2 phi (pi - phi)."""
    n = len(anchors)
    best = 0.0
    for i in range(n):
        for j in range(i + 1, n):
            phi = float(circ_dist(anchors[i], anchors[j]))
            best = max(best, 2 * phi * (np.pi - phi))
    return best


# ---------------------------------------------------------------------------
# Exact mu_H^2 of a flat triangle in L^inf_n, with gradient
# ---------------------------------------------------------------------------


def _hull_ccw(P: np.ndarray) -> list[int]:
    """Andrew's monotone chain; CCW hull indices, collinear points dropped."""
    order = np.lexsort((P[:, 1], P[:, 0]))

    def cross(o, a, b):
        return (P[a, 0] - P[o, 0]) * (P[b, 1] - P[o, 1]) - \
            (P[a, 1] - P[o, 1]) * (P[b, 0] - P[o, 0])

    lower: list[int] = []
    for i in order:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], i) <= 1e-15:
            lower.pop()
        lower.append(int(i))
    upper: list[int] = []
    for i in order[::-1]:
        while len(upper) >= 2 and cross(upper[-2], upper[-1], i) <= 1e-15:
            upper.pop()
        upper.append(int(i))
    return lower[:-1] + upper[:-1]


def triangle_muh(u: np.ndarray, v: np.ndarray, grad: bool = True):
    """mu_H^2 of the triangle spanned by u, v in L^inf_n, and d/du, d/dv."""
    n = len(u)
    uu, vv, uv = u @ u, v @ v, u @ v
    if uu * vv - uv * uv <= 1e-24 * max(uu * vv, 1e-300):
        return 0.0, np.zeros(n), np.zeros(n)
    W = np.stack([u, v], axis=1)
    keep = np.flatnonzero(np.hypot(W[:, 0], W[:, 1]) > 1e-15)
    pts = np.vstack([W[keep], -W[keep]])
    idx = np.concatenate([keep, keep])
    sgn = np.concatenate([np.ones(len(keep)), -np.ones(len(keep))])
    H = _hull_ccw(pts)
    h = pts[H]
    hn = np.roll(h, -1, axis=0)
    D = h[:, 0] * hn[:, 1] - h[:, 1] * hn[:, 0]
    X = np.stack([(hn[:, 1] - h[:, 1]) / D, (h[:, 0] - hn[:, 0]) / D], axis=1)
    Xn = np.roll(X, -1, axis=0)
    area = 0.5 * abs(np.sum(X[:, 0] * Xn[:, 1] - X[:, 1] * Xn[:, 0]))
    mu = 2.0 / area
    if not grad:
        return mu, None, None
    Xp = np.roll(X, 1, axis=0)  # facet k lies between X_{k-1} and X_k
    L = np.hypot(*(X - Xp).T)
    g_h = -(L / np.hypot(h[:, 0], h[:, 1]))[:, None] * 0.5 * (X + Xp)
    dA = np.zeros((n, 2))
    np.add.at(dA, idx[H], sgn[H][:, None] * g_h)
    dmu = -2.0 / area**2 * dA
    return mu, dmu[:, 0], dmu[:, 1]


def surface_muh(pos: np.ndarray, faces: np.ndarray, grad: bool = True):
    total = 0.0
    g = np.zeros_like(pos) if grad else None
    for a, b, c in faces:
        mu, du, dv = triangle_muh(pos[b] - pos[a], pos[c] - pos[a], grad)
        total += mu
        if grad:
            g[b] += du
            g[c] += dv
            g[a] -= du + dv
    return total, g


# ---------------------------------------------------------------------------
# Disk meshes spanning gamma_n
# ---------------------------------------------------------------------------


def disk_faces(M: int, R: int) -> np.ndarray:
    """Centre 0; ring r (1..R) vertex 1 + (r - 1) M + k; ring R is the boundary."""
    def vid(r, k):
        return 1 + (r - 1) * M + (k % M)
    F = [(0, vid(1, k), vid(1, k + 1)) for k in range(M)]
    for r in range(1, R):
        for k in range(M):
            F.append((vid(r, k), vid(r + 1, k), vid(r + 1, k + 1)))
            F.append((vid(r, k), vid(r + 1, k + 1), vid(r, k + 1)))
    return np.array(F)


def boundary_samples(anchors: np.ndarray, s: int):
    """Angles: each gap between consecutive breaks split into s equal pieces (exact on gamma)."""
    br = boundary_breaks(anchors)
    nxt = np.append(br[1:], br[0] + TWO_PI)
    ang = np.concatenate([br[j] + (nxt[j] - br[j]) * np.arange(s) / s for j in range(len(br))])
    return ang % TWO_PI


def cone_positions(anchors, ang, R, apex):
    gam = circ_dist(ang[:, None], anchors[None, :])
    return np.vstack([apex[None, :]] + [apex + (r / R) * (gam - apex) for r in range(1, R + 1)])


def hemisphere_positions(anchors, ang, R):
    """Kuratowski image of the round unit hemisphere (equator = boundary circle)."""
    b = np.stack([np.cos(anchors), np.sin(anchors), np.zeros_like(anchors)], axis=1)
    pts = [np.array([0.0, 0.0, 1.0])]
    for r in range(1, R + 1):
        phi = 0.5 * np.pi * r / R
        pts.extend(np.stack([np.sin(phi) * np.cos(ang), np.sin(phi) * np.sin(ang),
                             np.cos(phi) * np.ones_like(ang)], axis=1))
    P = np.array(pts)
    return np.arccos(np.clip(P @ b.T, -1.0, 1.0))


def minimize_disk(pos0, faces, n_fixed_from, maxiter):
    """Minimize total mu_H^2 over interior vertices (indices < n_fixed_from)."""
    n = pos0.shape[1]
    fixed = pos0[n_fixed_from:]

    def f(x):
        pos = np.vstack([x.reshape(-1, n), fixed])
        val, g = surface_muh(pos, faces)
        return val, g[:n_fixed_from].ravel()

    res = minimize(f, pos0[:n_fixed_from].ravel(), jac=True, method="L-BFGS-B",
                   options={"maxiter": maxiter, "ftol": 1e-12, "gtol": 1e-8})
    pos = np.vstack([res.x.reshape(-1, n), fixed])
    return float(surface_muh(pos, faces, grad=False)[0]), int(res.nit), pos


# ---------------------------------------------------------------------------
# Jobs
# ---------------------------------------------------------------------------


def cone_job(anchors: np.ndarray) -> dict:
    """Exact cone area from the optimized apex (R = 1 disk)."""
    n = len(anchors)
    ang = boundary_samples(anchors, 1)
    faces = disk_faces(len(ang), 1)
    gam = circ_dist(ang[:, None], anchors[None, :])
    centre = np.full(n, np.pi / 2)
    a0 = surface_muh(np.vstack([centre, gam]), faces, grad=False)[0]
    area, nit, pos = minimize_disk(np.vstack([centre, gam]), faces, 1, 2000)
    return {"cone_centre_pi_over_2": float(a0), "cone_optimized_apex": area,
            "apex": pos[0].tolist()}


def disk_job(args) -> dict:
    anchors, s, R, maxiter, start = args
    anchors = np.asarray(anchors)
    n = len(anchors)
    ang = boundary_samples(anchors, s)
    M = len(ang)
    faces = disk_faces(M, R)
    if start == "hemisphere":
        pos0 = hemisphere_positions(anchors, ang, R)
    else:
        pos0 = cone_positions(anchors, ang, R, np.full(n, np.pi / 2))
    a0 = float(surface_muh(pos0, faces, grad=False)[0])
    t0 = time.time()
    area, nit, _ = minimize_disk(pos0, faces, 1 + (R - 1) * M, maxiter)
    return {"n": n, "anchors": anchors.tolist(), "s": s, "R": R, "M": M,
            "faces": len(faces), "start": start, "start_area": a0, "min_area": area,
            "nit": nit, "seconds": round(time.time() - t0, 1)}


def check_gradients():
    rng = np.random.default_rng(3)
    for n in (2, 3, 8):
        u, v = rng.standard_normal(n), rng.standard_normal(n)
        mu, du, dv = triangle_muh(u, v)
        h = 1e-6
        err = 0.0
        for k in range(n):
            e = np.zeros(n)
            e[k] = h
            fu = (triangle_muh(u + e, v, False)[0] - triangle_muh(u - e, v, False)[0]) / (2 * h)
            fv = (triangle_muh(u, v + e, False)[0] - triangle_muh(u, v - e, False)[0]) / (2 * h)
            err = max(err, abs(fu - du[k]), abs(fv - dv[k]))
        lam = 0.5 * abs(u[0] * v[1] - u[1] * v[0]) if n == 2 else None
        print(f"n={n}: mu={mu:.6f} max grad error {err:.2e}"
              + (f" (Lebesgue {lam:.6f})" if lam is not None else ""))


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--ns", type=int, nargs="+", default=[2, 3, 4, 5, 6, 8, 12, 16])
    ap.add_argument("--levels", default="24:4,48:8,96:12",
                    help="mesh levels 'min boundary points:rings', comma separated")
    ap.add_argument("--maxiter", type=int, default=6000)
    ap.add_argument("--grid-step", type=int, default=12, help="n=3 gap grid: units of pi/step")
    ap.add_argument("--workers", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--check-grad", action="store_true")
    ap.add_argument("--out", default="benchmarks/linf_multi_point.json")
    args = ap.parse_args()
    if args.check_grad:
        check_gradients()
        return
    t_all = time.time()
    levels = [tuple(int(v) for v in lv.split(":")) for lv in args.levels.split(",")]

    def anchors_for(n):
        if n == 2:
            return np.array([0.0, np.pi / 2])  # the quarter pair; (0, pi) is degenerate
        if n % 2 == 0:
            # d(t, a + pi) = pi - d(t, a): the coordinate of an antipodal anchor is a
            # reflection of its partner's, so gamma_n (n even, equidistant) is isometric in
            # the sup norm to gamma on the n/2 anchors k pi/(n/2). Optimizing in the reduced
            # space gives the same areas and avoids permanent sup-norm ties, which stall
            # L-BFGS-B at the start (observed: 0-6 iterations for n = 6, 8, 12, 16).
            return np.pi * np.arange(n // 2) / (n // 2)
        return TWO_PI * np.arange(n) / n

    configs = {n: anchors_for(n) for n in args.ns}

    # 1. n = 3 anchor scan (gaps in units of pi/step, g1 <= g2 <= g3), coarsest level
    step = args.grid_step
    gaps = [(a, b, 2 * step - a - b) for a in range(1, 2 * step) for b in range(a, 2 * step)
            if 2 * step - a - b >= b]
    scan_anchors = [np.array([0.0, a * np.pi / step, (a + b) * np.pi / step]) for a, b, _ in gaps]
    m0, r0 = levels[0]

    def s_for(anchors, mmin):
        return max(1, int(np.ceil(mmin / len(boundary_breaks(anchors)))))

    with ProcessPoolExecutor(args.workers) as ex:
        scan = list(ex.map(disk_job, [(a, s_for(a, m0), r0, args.maxiter, "hemisphere")
                                      for a in scan_anchors]))
    for g, r in zip(gaps, scan):
        r["gaps_units"] = list(g)
        r["pair_lower_bound"] = pair_lower_bound(np.array(r["anchors"]))
    best3 = max(scan, key=lambda r: r["min_area"])
    print(f"n=3 scan: {len(scan)} anchor triples; best ceiling {best3['min_area']:.4f} "
          f"at gaps {best3['gaps_units']} (units of pi/{step})", flush=True)
    opt3 = np.array(best3["anchors"])
    if 3 not in configs or not np.allclose(np.sort(circ_dist(opt3, opt3[:, None]).ravel()),
                                           np.sort(circ_dist(configs[3], configs[3][:, None])
                                                   .ravel())):
        configs["3_optimized"] = opt3
    else:
        print("n=3: the best scanned triple is the equidistant one", flush=True)

    # 2. every configuration at every level, from both starts; plus cones
    jobs, keys = [], []
    for key, anchors in configs.items():
        for mmin, R in levels:
            for start in ("hemisphere", "cone"):
                jobs.append((anchors, s_for(anchors, mmin), R, args.maxiter, start))
                keys.append(key)
    with ProcessPoolExecutor(args.workers) as ex:
        runs = list(ex.map(disk_job, sorted(jobs, key=lambda j: -len(j[0]) * j[2]),
                           chunksize=1))
        cones = dict(zip(configs, ex.map(cone_job, configs.values())))
    raw = Path(args.out).with_suffix(".raw.json")
    raw.write_text(json.dumps({"scan": scan, "runs": runs,
                               "cones": {str(k): v for k, v in cones.items()}}) + "\n")

    results = {}
    for key, anchors in configs.items():
        mine = [r for r in runs if len(r["anchors"]) == len(anchors)
                and np.allclose(r["anchors"], anchors)]
        best_per_level = []
        for mmin, R in levels:
            lv = [r for r in mine if r["R"] == R]
            best_per_level.append(min(lv, key=lambda r: r["min_area"]))
        hemi = [r for r in mine if r["start"] == "hemisphere"]
        results[str(key)] = {
            "anchors": anchors.tolist(), "n": len(anchors),
            "pair_lower_bound": pair_lower_bound(anchors),
            "cone": cones[key],
            "hemisphere_image_area_by_level": [r["start_area"] for r in
                                               sorted(hemi, key=lambda r: r["R"])],
            "ceiling_by_level": [r["min_area"] for r in best_per_level],
            "ceiling": min(r["min_area"] for r in best_per_level),
            "runs": mine,
        }
        rr = results[str(key)]
        print(f"{str(key):12s} lower {rr['pair_lower_bound']:.4f}  cone "
              f"{cones[key]['cone_optimized_apex']:.4f}  ceiling by level "
              + " ".join(f"{v:.4f}" for v in rr["ceiling_by_level"])
              + f"  hemisphere image {rr['hemisphere_image_area_by_level'][-1]:.4f}", flush=True)

    # 3. n -> infinity along nested chains: least squares in 1/n^2 on the finest level
    def fit(ns):
        ys = [results[str(n)]["ceiling"] for n in ns if str(n) in results]
        xs = [1.0 / n**2 for n in ns if str(n) in results]
        if len(xs) < 2:
            return None
        A = np.vstack([np.ones(len(xs)), xs]).T
        c, *_ = np.linalg.lstsq(A, np.array(ys), rcond=None)
        return {"ns": [n for n in ns if str(n) in results], "limit": float(c[0]),
                "slope": float(c[1])}

    out = {
        "description": __doc__.split("\n\n")[0],
        "units": "Mathlib unnormalized mu_H^2; sup-norm plane = Lebesgue; Riemannian "
                 "surface = (4/pi) x area; round hemisphere = 8",
        "config": vars(args) | {"levels": levels},
        "reference": {"pi_sq_over_2": PI_SQ_2, "hemisphere_muH": HEMISPHERE_MUH,
                      "two_pi": TWO_PI, "fourteen_zeta3_over_pi": 5.356772273,
                      "fourteen_zeta3_over_pi_in_muH": 4 / np.pi * 5.356772273},
        "planar_projection_cap": "any 1-Lipschitz map into a normed plane X plus covering "
                                 "gives at most L^2 / (lambda(B) lambda(B°)) <= L^2/8 = pi^2/2 "
                                 "(Busemann isoperimetric inequality + planar Mahler)",
        "n3_scan": scan,
        "results": results,
        "extrapolation": {"chain_4_8_16": fit([4, 8, 16]), "chain_3_6_12": fit([3, 6, 12]),
                          "equidistant_all": fit([4, 5, 6, 8, 12, 16])},
        "total_seconds": round(time.time() - t_all, 1),
    }
    Path(args.out).write_text(json.dumps(out, indent=2) + "\n")
    print(f"\nSaved {args.out} ({out['total_seconds']} s)")
    print(json.dumps(out["extrapolation"], indent=1))


if __name__ == "__main__":
    main()

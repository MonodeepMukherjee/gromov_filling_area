"""Provable coordinate-pair projection bounds vs. L^inf_n ceilings, plus a fine metric search.

Part A (``--part projection``). For the equidistant n-anchor Kuratowski map
q_n : M -> L^inf_n and every anchor pair (i, j) at circle distance phi in (0, pi), the
coordinate projection pi_ij o q_n is 1-Lipschitz into the sup-norm plane and sends the
boundary onto a rectangle of area A_ij = 2 phi (pi - phi), which the image covers
(no-retraction argument, as in ``DiamondAreaBound``). Two kinds of lower bound follow:

* **Unconditional** (any compact metric filling): mu_H(M) >= max_ij A_ij. Combining several
  projections does not help for arbitrary sets: a cube of side d has every coordinate
  projection of area d^2 and mu_H-weight d^2, so sum_ij w_ij lambda(pi_ij S) <= (sum w) mu_H(S)
  is sharp, and the weighted average of the A_ij never beats the maximum.
* **Rectifiable** (e.g. Riemannian or Lipschitz-parametrized fillings, whose image is
  2-rectifiable): by the area formula, sum_ij w_ij lambda(pi_ij S) <= int_S sum_ij w_ij |p_ij|,
  where p_ij are the Pluecker coordinates of the approximate tangent plane P, while
  mu_H = int_S 4/lambda(B_P), B_P the sup-norm unit ball of P. So
      mu_H(M) >= sum_ij w_ij A_ij   whenever   sum_ij w_ij |p_ij(P)| <= 4/lambda(B_P) for all P.
  The best weights solve a semi-infinite LP, handled here by cutting planes with a
  multi-start search for the most violated plane. The search is numerical, so the
  resulting constant is an estimate of the provable rectifiable bound, not a certificate.

Part B (``--part metric``). Intrinsic-metric search on genus 0-2 meshes with n_b = 24
boundary vertices: L-BFGS-B with exact subgradients at penalty weights 1e2, 1e3 on the
k = 5 Steiner graph, then 1e4 on a finer k = 12 graph (the k = 5 graph misses shortcuts;
see the README), a Powell polish on the k = 12 objective, feasibility restoration, and
strict certification on the k = 48 Steiner graph.

Units: Part A uses Mathlib's unnormalized mu_H^2 (hemisphere = 8); Part B uses Riemannian
(Heron) area (hemisphere = 2 pi).

Usage:  .venv/bin/python3 scripts/discover_extremal_bound.py --part all
"""

from __future__ import annotations

import argparse
import itertools
import json
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

import numpy as np
from scipy.optimize import linprog, minimize

sys.path.insert(0, str(Path(__file__).resolve().parent))

TWO_PI = 2 * np.pi
HEMISPHERE_MUH = 8.0
ZETA3 = 1.2020569031595942
FOURTEEN_ZETA3_OVER_PI_MUH = 4 / np.pi * 14 * ZETA3 / np.pi


# ---------------------------------------------------------------------------
# Part A: projection bounds
# ---------------------------------------------------------------------------

def circ(a, b):
    d = abs(a - b) % TWO_PI
    return min(d, TWO_PI - d)


def ball_area(a: np.ndarray, b: np.ndarray) -> float:
    """Lebesgue area of {(s, t) : max_k |s a_k + t b_k| <= 1} (a, b orthonormal)."""
    keep = np.hypot(a, b) > 1e-14
    a, b = a[keep], b[keep]
    n = len(a)
    i, j = np.triu_indices(n, 1)
    det = a[i] * b[j] - a[j] * b[i]
    ok = np.abs(det) > 1e-13
    i, j, det = i[ok], j[ok], det[ok]
    pts = []
    for c1, c2 in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
        s = (c1 * b[j] - c2 * b[i]) / det
        t = (c2 * a[i] - c1 * a[j]) / det
        pts.append(np.c_[s, t])
    P = np.vstack(pts)
    val = np.abs(np.outer(P[:, 0], a) + np.outer(P[:, 1], b)).max(axis=1)
    P = P[val <= 1 + 1e-9]
    ang = np.arctan2(P[:, 1], P[:, 0])
    P = P[np.argsort(ang)]
    x, y = P[:, 0], P[:, 1]
    return 0.5 * abs(float(np.sum(x * np.roll(y, -1) - np.roll(x, -1) * y)))


def plane_from(v: np.ndarray, n: int):
    X = v.reshape(2, n)
    q, _ = np.linalg.qr(X.T)
    return q[:, 0], q[:, 1]


def pluecker_abs(a, b, pairs):
    i, j = pairs[:, 0], pairs[:, 1]
    return np.abs(a[i] * b[j] - a[j] * b[i])


def violation_ratio(v, w, pairs, n):
    """sum_ij w_ij |p_ij(P)| / (4 / lambda(B_P)) for the plane spanned by v."""
    a, b = plane_from(v, n)
    return float(w @ pluecker_abs(a, b, pairs)) * ball_area(a, b) / 4.0


def projection_bound(n: int, rng: np.random.Generator, rounds: int = 60,
                     starts: int = 12) -> dict:
    anchors = TWO_PI * np.arange(n) / n
    pairs, areas = [], []
    for i, j in itertools.combinations(range(n), 2):
        phi = circ(anchors[i], anchors[j])
        if 1e-9 < phi < np.pi - 1e-9:
            pairs.append((i, j))
            areas.append(2 * phi * (np.pi - phi))
    pairs, areas = np.array(pairs), np.array(areas)
    m = len(pairs)
    # constraint rows |p_ij(P)| * lambda(B_P) / 4 for each cut plane P
    cuts = []

    def add_cut(v):
        a, b = plane_from(v, n)
        cuts.append(pluecker_abs(a, b, pairs) * ball_area(a, b) / 4.0)

    for i, j in itertools.combinations(range(n), 2):  # coordinate planes
        v = np.zeros(2 * n)
        v[i], v[n + j] = 1.0, 1.0
        add_cut(v)
    add_cut(np.r_[np.ones(n), np.arange(n) - (n - 1) / 2])
    for _ in range(4 * n):
        add_cut(rng.standard_normal(2 * n))
    history, worst = [], []
    for rnd in range(rounds):
        res = linprog(-areas, A_ub=np.array(cuts), b_ub=np.ones(len(cuts)),
                      bounds=[(0, None)] * m, method="highs")
        w = res.x
        best_r, best_v = -np.inf, None
        # prescreen random planes, then polish the most violated ones (plus the last worst)
        pool = rng.standard_normal((40 * starts, 2 * n))
        scores = np.array([violation_ratio(v, w, pairs, n) for v in pool])
        cands = list(pool[np.argsort(-scores)[:starts]]) + worst[-4:]
        for v0 in cands:
            r = minimize(lambda v: -violation_ratio(v, w, pairs, n), v0, method="Nelder-Mead",
                         options={"maxiter": 200 * n, "xatol": 1e-9, "fatol": 1e-12,
                                  "adaptive": True})
            if -r.fun > best_r:
                best_r, best_v = -r.fun, r.x
        history.append({"round": rnd, "lp_value": float(-res.fun), "max_ratio": best_r})
        if best_r <= 1 + 1e-7:
            break
        add_cut(best_v)
        worst.append(best_v)
    lp_value = float(-res.fun)
    bound = lp_value / max(1.0, best_r)
    a, b = plane_from(best_v, n)
    return {
        "n": n, "pairs": len(pairs), "unconditional_max_pair": float(areas.max()),
        "uniform_weight_constant": None,
        "rectifiable_lp_value": lp_value, "final_max_violation_ratio": best_r,
        "rectifiable_bound": bound, "weights": w.tolist(),
        "pair_areas": areas.tolist(), "pair_list": pairs.tolist(),
        "worst_plane": [a.tolist(), b.tolist()], "cuts": len(cuts), "rounds": history,
    }


def uniform_constant(n: int, rng: np.random.Generator, starts: int = 64) -> float:
    """min over planes of (4/lambda(B_P)) / sum_{i<j} |p_ij(P)| (all pairs, unit weights)."""
    pairs = np.array(list(itertools.combinations(range(n), 2)))
    w = np.ones(len(pairs))
    best = np.inf
    for _ in range(starts):
        r = minimize(lambda v: -violation_ratio(v, w, pairs, n), rng.standard_normal(2 * n),
                     method="Nelder-Mead", options={"maxiter": 400 * n})
        best = min(best, 1.0 / -r.fun)
    return best


def part_projection(ns, workers, seed=11) -> dict:
    ceil = {}
    lp = Path("benchmarks/linf_multi_point.json")
    if lp.exists():
        d = json.loads(lp.read_text())
        ceil = {int(k): v["ceiling"] for k, v in d["results"].items() if k.isdigit()}
        if 5 in ceil:
            ceil.setdefault(10, ceil[5])  # gamma_10 is sup-isometric to gamma_5
    with ProcessPoolExecutor(workers) as ex:
        futs = {n: ex.submit(projection_bound, n, np.random.default_rng(seed + n))
                for n in ns}
        out = {n: f.result() for n, f in futs.items()}
    out[3]["uniform_weight_constant"] = uniform_constant(3, np.random.default_rng(seed))
    rows = []
    for n in ns:
        r = out[n]
        r["full_linf_ceiling"] = ceil.get(n)
        rows.append(r)
        print(f"n={n:2d}  unconditional {r['unconditional_max_pair']:.4f}  rectifiable "
              f"{r['rectifiable_bound']:.4f} (LP {r['rectifiable_lp_value']:.4f}, max ratio "
              f"{r['final_max_violation_ratio']:.6f}, {len(r['rounds'])} rounds)  ceiling "
              f"{ceil.get(n, float('nan')):.4f}", flush=True)
    return {
        "units": "Mathlib unnormalized mu_H^2; hemisphere = 8",
        "reference": {"pi_sq_over_2": np.pi**2 / 2, "sixteen_pi_sq_over_27": 16 * np.pi**2 / 27,
                      "hemisphere_muH": HEMISPHERE_MUH,
                      "fourteen_zeta3_over_pi_muH": FOURTEEN_ZETA3_OVER_PI_MUH},
        "n3_uniform_constant_expected": 4 / 9,
        "results": {str(r["n"]): r for r in rows},
    }


# ---------------------------------------------------------------------------
# Part B: metric search
# ---------------------------------------------------------------------------

def metric_job(genus: int, restart: int, cfg: dict) -> dict:
    from discover_extremal_metrics import GradFillingProblem, structure
    from explore_genus2 import build_mesh, heron_area_grad

    t_all = time.time()
    mesh = build_mesh(genus, n_b=cfg["n_boundary"])
    coarse = GradFillingProblem(mesh, cfg["k_coarse"], cfg["certify_k"], cfg["angle_margin"])
    fine = GradFillingProblem(mesh, cfg["k_fine"], cfg["certify_k"], cfg["angle_margin"])
    fine.cert = coarse.cert  # share the expensive certification graph
    tol = cfg["strict_tol"]
    jit = cfg["jitters"][restart % len(cfg["jitters"])]
    rng = None if restart == 0 else np.random.default_rng(9100 * (genus + 1) + restart)
    tag = f"g={genus} r={restart}"
    x0, c0 = coarse.feasible_start(tol, rng, jitter=jit)
    start = {"scale": c0, "jitter": jit, "area": float(
        heron_area_grad(coarse.lengths(x0), mesh.face_edges)[0])}
    print(f"  [{tag}] start A={start['area']:.4f} jitter={jit}", flush=True)
    x, stages = x0, []
    for prob, w, it in ((coarse, 1e2, cfg["maxiter"]), (coarse, 1e3, cfg["maxiter"]),
                        (fine, 1e4, cfg["maxiter_fine"])):
        x, info = prob.run_stage(x, w, it, max_cycles=cfg["max_cycles"])
        info["steiner_k"] = prob.steiner_k
        stages.append(info)
        print(f"  [{tag}] k={prob.steiner_k} w={w:.0e} A={info['area']:.4f} "
              f"nit={info['nit']} ({info['seconds']} s)", flush=True)
    x_pre, area_pre = x, stages[-1]["area"]
    # Powell polish of the fine penalized objective (derivative-free, budgeted)
    t0 = time.time()
    from scipy.optimize import minimize as _min
    f_fine = lambda z: fine.objective_grad(z, 1e4)[0]  # noqa: E731
    f0 = f_fine(x)
    res = _min(f_fine, x, method="Powell", bounds=[(1e-3, None)] * len(x),
               options={"maxfev": cfg["powell_maxfev"], "xtol": 1e-7, "ftol": 1e-12})
    if res.fun < f0:
        x = res.x
    powell = {"objective_before": float(f0), "objective_after": float(min(f0, res.fun)),
              "nfev": int(res.nfev), "seconds": round(time.time() - t0, 1),
              "area": float(heron_area_grad(fine.lengths(x), mesh.face_edges)[0])}
    print(f"  [{tag}] Powell A={powell['area']:.4f} ({powell['seconds']} s)", flush=True)
    t0 = time.time()
    x_fin, how = fine.restore(x, x0, tol)
    final = {**how, "seconds": round(time.time() - t0, 1)}
    final.update(fine.certify(x_fin, tol))
    final["certify_k"] = cfg["certify_k"]
    final["k_certify_violation"] = final.pop("k16_violation")
    final["structure"] = structure(mesh, fine.lengths(x_fin))
    print(f"  [{tag}] final A={final['area']:.4f} A/2pi={final['area_over_2pi']:.4f} "
          f"k{cfg['certify_k']}={final['k_certify_violation']:.1e} "
          f"lb={final['exact_lower_bound']:.1e} strict={final['strictly_feasible']} "
          f"({round(time.time() - t_all)} s)", flush=True)
    return {"genus": genus, "restart": restart, "mesh": mesh.info, "start": start,
            "stages": stages, "area_before_powell": area_pre, "powell": powell,
            "final": final, "final_edge_lengths": fine.lengths(x_fin).tolist(),
            "seconds": round(time.time() - t_all, 1)}


def part_metric(cfg: dict, out_path: Path, partial: dict) -> dict:
    jobs = [(g, r) for g, cnt in zip((0, 1, 2), cfg["runs_per_genus"]) for r in range(cnt)]
    print(f"metric search: {len(jobs)} runs on {cfg['workers']} workers", flush=True)
    runs = []
    with ProcessPoolExecutor(cfg["workers"]) as ex:
        futs = [ex.submit(metric_job, g, r, cfg) for g, r in jobs]
        for fut in as_completed(futs):
            runs.append(fut.result())
            partial["metric"] = {"partial": True, "runs": runs}
            out_path.write_text(json.dumps(partial) + "\n")
    runs.sort(key=lambda r: (r["genus"], r["restart"]))
    summary = {}
    for g in (0, 1, 2):
        mine = [r for r in runs if r["genus"] == g]
        ok = [r for r in mine if r["final"]["strictly_feasible"]]
        areas = sorted(r["final"]["area"] for r in ok)
        summary[str(g)] = {
            "runs": len(mine), "strictly_feasible": len(ok),
            "best_area": areas[0] if ok else None,
            "best_area_over_2pi": areas[0] / TWO_PI if ok else None,
            "median_area": float(np.median(areas)) if ok else None,
            "areas": areas,
            "all_above_2pi": bool(ok and areas[0] > TWO_PI),
            "best_before_powell": min(r["area_before_powell"] for r in mine),
            "best_after_powell": min(r["powell"]["area"] for r in mine),
        }
        s = summary[str(g)]
        if ok:
            print(f"genus {g}: {len(ok)}/{len(mine)} strict, best A={s['best_area']:.5f} "
                  f"(A/2pi={s['best_area_over_2pi']:.5f}), median {s['median_area']:.4f}",
                  flush=True)
    return {"config": cfg, "summary": summary, "runs": runs}


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--part", choices=["projection", "metric", "all"], default="all")
    ap.add_argument("--ns", type=int, nargs="+", default=[3, 4, 5, 6, 8, 10, 12, 16])
    ap.add_argument("--n-boundary", type=int, default=24)
    ap.add_argument("--runs-per-genus", type=int, nargs=3, default=[12, 10, 10])
    ap.add_argument("--jitters", type=float, nargs="+", default=[0.0, 0.03, 0.06, 0.1])
    ap.add_argument("--maxiter", type=int, default=10000)
    ap.add_argument("--maxiter-fine", type=int, default=3000)
    ap.add_argument("--max-cycles", type=int, default=60)
    ap.add_argument("--powell-maxfev", type=int, default=2000)
    ap.add_argument("--k-coarse", type=int, default=5)
    ap.add_argument("--k-fine", type=int, default=12)
    ap.add_argument("--certify-k", type=int, default=48)
    ap.add_argument("--angle-margin", type=float, default=1e-3)
    ap.add_argument("--strict-tol", type=float, default=1e-10)
    ap.add_argument("--workers", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--out", default="benchmarks/extremal_bound_discovery.json")
    args = ap.parse_args()
    cfg = vars(args)
    out_path = Path(args.out)
    t0 = time.time()
    data = json.loads(out_path.read_text()) if out_path.exists() else {}
    data["description"] = __doc__.split("\n\n")[0]
    if args.part in ("projection", "all"):
        data["projection"] = part_projection(args.ns, args.workers)
        out_path.write_text(json.dumps(data, indent=1) + "\n")
    if args.part in ("metric", "all"):
        data["metric"] = part_metric(cfg, out_path, data)
    data["config"] = cfg
    data["total_seconds_last_part"] = round(time.time() - t0, 1)
    out_path.write_text(json.dumps(data, indent=1) + "\n")
    print(f"Saved {out_path} ({data['total_seconds_last_part']} s)")


if __name__ == "__main__":
    main()

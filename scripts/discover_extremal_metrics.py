"""Gradient-based discovery of extremal discrete fillings of S^1 (genus 0-2).

This is the gradient counterpart of ``explore_genus2.py``. It uses the same meshes
(octahedron or connected sums of 7-vertex tori, one face punched out, one midpoint
subdivision, a fan collar out to an n_b-ring and a second ring of 4-split quads)
and the same intrinsic-edge-length (piecewise-flat) metric. The derivative-free
Powell / Nelder-Mead search is replaced by L-BFGS-B with exact analytical
(sub)gradients (``jac=True``); no finite differences are used in the optimizer.

Objective, for a penalty weight ``w``:

    Heron area                                        dA/dl:  l_a (l_b^2 + l_c^2 - l_a^2) / (8 K)
  + triangle log barrier on l_a + l_b - l_c - eps     dB/ds:  -BARRIER / s  (stiff C^1 ext.)
  + w * sum_i max(0, pi + m - theta(b_i))^2           dtheta/dl from the law of cosines
  + w * sum_ij max(0, d_S1(b_i, b_j) - d_5(b_i, b_j))^2

``d_5`` is the k = 5 Steiner-graph distance. Its subgradient comes from the
shortest-path tree: ``scipy.sparse.csgraph.dijkstra(..., return_predecessors=True)``
gives each violated path, and every segment on it contributes
``-2 w (d_S1 - d_5) * dw_seg/dl`` to the three edges of the face that holds the
segment (``w_seg`` is the segment's length in that face, unfolded in the plane).
Where the shortest path is unique, this is the exact gradient of the distance.

Schedule per (genus, restart), all jobs in parallel:

1. Strictly feasible hemisphere-profile start (as in ``explore_genus2.py``).
2. Three L-BFGS-B stages with ``w = 1e2, 1e3, 1e4`` (penalty continuation).
3. Feasibility polishing: the cheaper of a radial rescale and a blend toward the
   start, by bisection, with k = 16 violation <= ``--strict-tol`` (1e-10).
4. Certification: k = 16 Steiner violation <= 1e-10, exact corner-cut lower
   bound == 0, triangle slacks >= eps, every boundary cone angle >= pi.

A Steiner graph only upper-bounds intrinsic distance, so certification is strong
numerical evidence of feasibility, not a proof.

Usage:  .venv/bin/python3 scripts/discover_extremal_metrics.py --n-boundary 16 --restarts 4
        .venv/bin/python3 scripts/discover_extremal_metrics.py --check-grad
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

import numpy as np
from scipy.optimize import minimize
from scipy.sparse.csgraph import dijkstra

sys.path.insert(0, str(Path(__file__).resolve().parent))
from explore_genus2 import (  # noqa: E402
    BARRIER,
    EPS_TRI,
    EPS_LEN,
    TWO_PI,
    FillingProblem,
    Mesh,
    PathDistance,
    add_boundary_strip,
    add_collar,
    build_mesh,
    closed_surface,
    heron_area_grad,
    subdivide,
)

BARRIER_DELTA = 1e-3  # log barrier continues linearly below this slack
# Stiff quadratic below ``BARRIER_DELTA``. Heron area has slope ~ 1/sqrt(slack) as a
# triangle collapses, so a soft extension lets L-BFGS-B step into degenerate faces.
BARRIER_STIFF = 1e8
INVALID_VALUE = 1e12  # returned for invalid triangles, so line searches backtrack
STAGES = (1e2, 1e3, 1e4)


# ---------------------------------------------------------------------------
# Exact analytical gradients
# ---------------------------------------------------------------------------


def barrier_grad(slack: np.ndarray, delta: float = BARRIER_DELTA):
    """Log barrier ``-BARRIER * log(slack)``, C^1-extended below ``delta``, and its derivative.

    Below ``delta`` it continues linearly plus a stiff quadratic ``BARRIER_STIFF * out^2``.
    """
    inner = np.maximum(slack, delta)
    out = np.maximum(delta - slack, 0.0)
    val = BARRIER * (-np.log(inner) + out / delta).sum() + BARRIER_STIFF * (out @ out)
    d = np.where(slack > delta, -BARRIER / inner, -BARRIER / delta) \
        - 2.0 * BARRIER_STIFF * out
    return float(val), d


def corner_angles_grad(lengths: np.ndarray, faces: np.ndarray, face_edges: np.ndarray,
                       n_vertices: int, coef: np.ndarray):
    """Cone angles at all vertices and ``sum_v coef[v] * dtheta(v)/dl`` over edges.

    For the corner ``alpha`` opposite side ``a`` (adjacent sides ``b``, ``c``) and
    face area ``K``, the law of cosines gives
    ``dalpha/da = a / (2K)``, ``dalpha/db = -(b - c cos alpha) / (2K)``,
    ``dalpha/dc = -(c - b cos alpha) / (2K)``.
    """
    la, lb, lc = (lengths[face_edges[:, s]] for s in range(3))
    q = 2 * (la * la * lb * lb + lb * lb * lc * lc + lc * lc * la * la) \
        - la**4 - lb**4 - lc**4
    two_k = 0.5 * np.sqrt(np.maximum(q, 1e-28))  # 2 * area
    tot = np.zeros(n_vertices)
    grad = np.zeros_like(lengths)
    for k, (x, y, z) in enumerate(((la, lb, lc), (lb, lc, la), (lc, la, lb))):
        cos = np.clip((y * y + z * z - x * x) / np.maximum(2 * y * z, 1e-15), -1.0, 1.0)
        np.add.at(tot, faces[:, k], np.arccos(cos))
        c = coef[faces[:, k]]
        ex, ey, ez = (face_edges[:, (k + s) % 3] for s in range(3))
        np.add.at(grad, ex, c * x / two_k)
        np.add.at(grad, ey, -c * (y - z * cos) / two_k)
        np.add.at(grad, ez, -c * (z - y * cos) / two_k)
    return tot, grad


class GradPathDistance(PathDistance):
    """Steiner-graph boundary distances with shortest-path-tree subgradients."""

    def __init__(self, mesh: Mesh, k: int):
        super().__init__(mesh, k)
        m, n = len(self.faces_of), self.n_nodes
        r, c = self.rows[:m], self.cols[:m]
        keys = np.concatenate([r * n + c, c * n + r])
        order = np.argsort(keys)
        self.keys = keys[order]
        self.key_seg = np.concatenate([np.arange(m), np.arange(m)])[order]

    def segment_geometry(self, lengths: np.ndarray):
        """Segment lengths and their partials w.r.t. ``(l_a, l_b, l_c)`` of their face.

        Face layout: ``A = (0, 0)``, ``B = (l_c, 0)``, ``C = (x, y)`` with
        ``x = (l_b^2 + l_c^2 - l_a^2) / (2 l_c)`` and ``y = sqrt(l_b^2 - x^2)``. A
        segment with barycentric difference ``(d0, d1, d2)`` is the vector
        ``v = (d1 l_c + d2 x, d2 y)`` and has length ``|v|``.
        """
        fe = self.mesh.face_edges
        lengths = np.maximum(lengths, 1e-9)
        la, lb, lc = (lengths[fe[:, s]] for s in range(3))
        x = (lb * lb + lc * lc - la * la) / (2 * lc)
        y = np.sqrt(np.maximum(lb * lb - x * x, 1e-24))
        dx = np.stack([-la / lc, lb / lc, 1.0 - x / lc], axis=1)
        dy = np.stack([x * la / (lc * y), lb * (1.0 - x / lc) / y,
                       -x * (1.0 - x / lc) / y], axis=1)
        f = self.faces_of
        d1, d2 = self.dw[:, 1], self.dw[:, 2]
        vx, vy = d1 * lc[f] + d2 * x[f], d2 * y[f]
        w = np.maximum(np.hypot(vx, vy), 1e-12)
        ux, uy = vx / w, vy / w
        dvx = d2[:, None] * dx[f]
        dvx[:, 2] += d1
        dvy = d2[:, None] * dy[f]
        dw = ux[:, None] * dvx + uy[:, None] * dvy
        return w, dw

    def hinge_penalty_grad(self, lengths: np.ndarray, weight: float):
        """``weight * sum max(0, d_S1 - d)^2`` and its subgradient over edges."""
        w, dw = self.segment_geometry(lengths)
        g = self.graph.copy()
        g.data = w[self.order]
        dist, pred = dijkstra(g, directed=True, indices=self.bnd, return_predecessors=True)
        d = dist[self.ii, self.bnd[self.jj]]
        hinge = np.maximum(0.0, self.target - d)
        seg_coef = np.zeros(len(w))
        n = self.n_nodes
        for p in np.flatnonzero(hinge > 0):
            i, src, node = self.ii[p], self.bnd[self.ii[p]], self.bnd[self.jj[p]]
            path = [node]
            while node != src:
                node = pred[i, node]
                path.append(node)
            path = np.array(path)
            seg = self.key_seg[np.searchsorted(self.keys, path[1:] * n + path[:-1])]
            # d(hinge^2)/dl = 2 hinge * (-dd/dl) = 2 (d - d_S1) dd/dl
            np.add.at(seg_coef, seg, -2.0 * weight * hinge[p])
        grad = np.zeros_like(lengths)
        fe = self.mesh.face_edges[self.faces_of]
        for s in range(3):
            np.add.at(grad, fe[:, s], seg_coef * dw[:, s])
        return float(weight * hinge @ hinge), grad


class GradFillingProblem(FillingProblem):
    def __init__(self, mesh: Mesh, steiner_k: int = 5, certify_k: int = 16,
                 angle_margin: float = 1e-3):
        super().__init__(mesh, steiner_k, certify_k)
        self.gpd = GradPathDistance(mesh, steiner_k)
        self.angle_margin = angle_margin
        self.is_bnd = np.zeros(mesh.n_vertices, dtype=bool)
        self.is_bnd[self.bnd] = True
        self.nfev = 0

    def objective_grad(self, x: np.ndarray, weight: float):
        """Penalized objective and its exact gradient w.r.t. the free edge lengths."""
        self.nfev += 1
        m = self.mesh
        ell = self.lengths(x)
        slack = self.T @ x + self.T_const  # l_a + l_b - l_c - EPS_TRI
        bval, bd = barrier_grad(slack)
        if slack.min() <= -EPS_TRI:  # a genuinely invalid triangle: push back
            return INVALID_VALUE + bval, self.T.T @ bd
        area, g = heron_area_grad(ell, m.face_edges)
        dval, dg = self.gpd.hinge_penalty_grad(ell, weight)
        # boundary cone angles: first pass for values, second for the gradient
        tot, _ = corner_angles_grad(ell, m.faces, m.face_edges, m.n_vertices,
                                    np.zeros(m.n_vertices))
        hinge = np.where(self.is_bnd,
                         np.maximum(0.0, np.pi + self.angle_margin - tot), 0.0)
        _, ag = corner_angles_grad(ell, m.faces, m.face_edges, m.n_vertices,
                                   -2.0 * weight * hinge)
        val = area + bval + dval + weight * float(hinge @ hinge)
        grad = (g + dg + ag)[self.free] + self.T.T @ bd
        return val, grad

    def run_stage(self, x0: np.ndarray, weight: float, maxiter: int,
                  max_cycles: int = 40, rel_tol: float = 1e-9):
        """L-BFGS-B at a fixed penalty weight, restarted with fresh memory.

        The Steiner distance term is only piecewise smooth (shortest paths switch),
        which corrupts the quasi-Newton memory and makes L-BFGS-B stop early with
        tiny steps. Each cycle restarts it from the current point until a cycle
        improves the objective by less than ``rel_tol`` (relative) or the total
        iteration budget ``maxiter`` is spent.
        """
        self.nfev = 0
        t0 = time.time()
        x, f = x0, self.objective_grad(x0, weight)[0]
        nit, cycles, msg, jac = 0, 0, "", None
        while cycles < max_cycles and nit < maxiter:
            res = minimize(self.objective_grad, x, args=(weight,), jac=True,
                           method="L-BFGS-B", bounds=[(EPS_LEN, None)] * len(x),
                           options={"maxiter": maxiter - nit, "maxfun": 4 * maxiter,
                                    "ftol": 1e-13, "gtol": 1e-9, "maxcor": 30})
            cycles += 1
            nit += int(res.nit)
            msg = str(res.message)
            improved = res.fun < f
            if improved:
                x, jac = res.x, res.jac
            gain = (f - res.fun) / max(1.0, abs(f))
            f = min(f, float(res.fun))
            if not improved or gain < rel_tol:
                break
        if jac is None:
            jac = self.objective_grad(x, weight)[1]
        info = {"penalty_weight": weight, "message": msg, "lbfgsb_cycles": cycles,
                "nit": nit, "nfev": self.nfev, "objective": f,
                "grad_inf_norm": float(np.abs(jac).max()),
                "seconds": round(time.time() - t0, 2)}
        info.update(self.metrics(x))
        return x, info


# ---------------------------------------------------------------------------
# Structural analysis
# ---------------------------------------------------------------------------


def region_face_counts(genus: int, n_b: int) -> tuple[int, int]:
    """Number of core (handle-region) faces and of first-collar faces in ``build_mesh``.

    ``build_mesh`` keeps face order through ``orient``, so faces ``[0, n_core)`` are
    the subdivided punctured closed surface, the next ``n_c1`` the fan collar, and
    the rest the second (quad-strip) collar ring.
    """
    surf = subdivide(closed_surface(genus)[1:])
    n_core = len(surf)
    surf, _ = add_collar(surf, n_b)
    n_c1 = len(surf) - n_core
    add_boundary_strip(surf)
    return n_core, n_c1


def structure(mesh: Mesh, ell: np.ndarray) -> dict:
    n_b = len(mesh.boundary)
    n_core, _ = region_face_counts(mesh.genus, n_b)
    fe = mesh.face_edges
    la, lb, lc = (ell[fe[:, s]] for s in range(3))
    q = 2 * (la * la * lb * lb + lb * lb * lc * lc + lc * lc * la * la) \
        - la**4 - lb**4 - lc**4
    area = 0.25 * np.sqrt(np.maximum(q, 0.0))
    core = np.zeros(len(fe), dtype=bool)
    core[:n_core] = True
    core_edges = np.zeros(len(ell), dtype=bool)
    core_edges[np.unique(fe[core])] = True
    a_core, a_col = float(area[core].sum()), float(area[~core].sum())
    l_core, l_col = float(ell[core_edges].mean()), float(ell[~core_edges].mean())
    return {
        "handle_region": "core faces (subdivided punctured closed surface); collar = "
                         "fan collar + quad-strip ring",
        "handle_faces": int(core.sum()), "collar_faces": int((~core).sum()),
        "handle_edges": int(core_edges.sum()), "collar_edges": int((~core_edges).sum()),
        "handle_area": a_core, "collar_area": a_col,
        "handle_area_fraction": a_core / (a_core + a_col),
        "handle_to_collar_area_ratio": a_core / a_col,
        "handle_to_collar_mean_face_area_ratio":
            (a_core / core.sum()) / (a_col / (~core).sum()),
        "handle_mean_edge_length": l_core, "collar_mean_edge_length": l_col,
        "handle_to_collar_mean_edge_length_ratio": l_core / l_col,
        "handle_total_edge_length_to_collar_area": float(ell[core_edges].sum()) / a_col,
    }


# ---------------------------------------------------------------------------
# Gradient check (diagnostic only: finite differences never enter the optimizer)
# ---------------------------------------------------------------------------


def check_gradients(genus: int, n_b: int, h: float = 1e-6, n_dirs: int = 6) -> None:
    mesh = build_mesh(genus, n_b=n_b)
    prob = GradFillingProblem(mesh)
    x0, _ = prob.feasible_start(1e-10)
    rng = np.random.default_rng(7)
    # shrink toward violation so every penalty term is active
    for scale in (1.0, 0.6):
        x = scale * x0 * np.exp(0.05 * rng.standard_normal(len(x0)))
        f, g = prob.objective_grad(x, 1e3)
        errs = []
        for _ in range(n_dirs):
            v = rng.standard_normal(len(x))
            v /= np.linalg.norm(v)
            fd = (prob.objective_grad(x + h * v, 1e3)[0]
                  - prob.objective_grad(x - h * v, 1e3)[0]) / (2 * h)
            errs.append(abs(fd - g @ v) / max(1.0, abs(fd)))
        print(f"genus {genus} scale {scale}: f={f:.6f} |g|={np.linalg.norm(g):.3e} "
              f"max rel. directional error={max(errs):.2e}")


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------


def run_restart(genus: int, restart: int, cfg: dict) -> dict:
    t_all = time.time()
    mesh = build_mesh(genus, n_b=cfg["n_boundary"])
    prob = GradFillingProblem(mesh, cfg["steiner_k"], cfg["certify_k"], cfg["angle_margin"])
    tol = cfg["strict_tol"]
    seed = None if restart == 0 else 1000 * genus + restart
    rng = None if seed is None else np.random.default_rng(seed)
    tag = f"g={genus} r={restart}"

    x0, c0 = prob.feasible_start(tol, rng, jitter=cfg["jitter"])
    start = {"hemisphere_scale_c": c0}
    start.update(prob.certify(x0, tol))
    print(f"  [{tag} start ] A={start['area']:.4f} k16={start['k16_violation']:.1e}",
          flush=True)

    x, stages = x0, []
    for w in STAGES:
        x, info = prob.run_stage(x, w, cfg["maxiter"])
        stages.append(info)
        print(f"  [{tag} w={w:.0e}] A={info['area']:.4f} "
              f"k5={info[f'k{prob.steiner_k}_violation']:.1e} "
              f"ang={info['min_boundary_angle_over_pi']:.4f}pi nit={info['nit']} "
              f"({info['seconds']} s)", flush=True)

    t0 = time.time()
    x_fin, how = prob.restore(x, x0, tol)
    final = {**how, "seconds": round(time.time() - t0, 2)}
    final.update(prob.certify(x_fin, tol))
    ell = prob.lengths(x_fin)
    final["structure"] = structure(mesh, ell)
    print(f"  [{tag} final ] {how} A={final['area']:.4f} "
          f"A/2pi={final['area_over_2pi']:.4f} k16={final['k16_violation']:.1e} "
          f"lb={final['exact_lower_bound']:.1e} strict={final['strictly_feasible']}",
          flush=True)
    return {"genus": genus, "restart": restart, "seed": seed, "mesh": mesh.info,
            "free_edges": int(prob.free.sum()), "feasible_start": start,
            "stages": stages, "final": final, "final_edge_lengths": ell.tolist(),
            "seconds": round(time.time() - t_all, 2)}


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--n-boundary", type=int, default=16)
    ap.add_argument("--restarts", type=int, default=4)
    ap.add_argument("--genera", type=int, nargs="+", default=[0, 1, 2])
    ap.add_argument("--maxiter", type=int, default=3000, help="L-BFGS-B iterations per stage")
    ap.add_argument("--jitter", type=float, default=0.25)
    ap.add_argument("--angle-margin", type=float, default=1e-3,
                    help="the cone-angle hinge targets pi + margin")
    ap.add_argument("--strict-tol", type=float, default=1e-10,
                    help="required k = 16 violation after feasibility polishing")
    ap.add_argument("--steiner-k", type=int, default=5)
    ap.add_argument("--certify-k", type=int, default=16)
    ap.add_argument("--workers", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--check-grad", action="store_true",
                    help="compare analytic gradients with central differences and exit")
    ap.add_argument("--out", default="benchmarks/extremal_discovery.json")
    args = ap.parse_args()
    cfg = vars(args)

    if args.check_grad:
        for g in args.genera:
            check_gradients(g, args.n_boundary)
        return

    t0 = time.time()
    jobs = [(g, r) for g in sorted(args.genera, reverse=True) for r in range(args.restarts)]
    print(f"{len(jobs)} jobs on {args.workers} workers", flush=True)
    runs = []
    with ProcessPoolExecutor(max_workers=args.workers) as ex:
        futs = [ex.submit(run_restart, g, r, cfg) for g, r in jobs]
        for fut in as_completed(futs):
            runs.append(fut.result())
    runs.sort(key=lambda r: (r["genus"], r["restart"]))

    best = {}
    for g in args.genera:
        ok = [r for r in runs if r["genus"] == g and r["final"]["strictly_feasible"]]
        if not ok:
            best[str(g)] = None
            print(f"genus {g}: no strictly feasible restart")
            continue
        b = min(ok, key=lambda r: r["final"]["area"])
        f = b["final"]
        best[str(g)] = {"restart": b["restart"], "area": f["area"],
                        "area_over_2pi": f["area_over_2pi"],
                        "k16_violation": f["k16_violation"],
                        "exact_lower_bound": f["exact_lower_bound"],
                        "min_boundary_angle_over_pi": f["min_boundary_angle_over_pi"],
                        "structure": f["structure"]}
        s = f["structure"]
        print(f"genus {g}: A={f['area']:.4f} A/2pi={f['area_over_2pi']:.4f} "
              f"handle/collar area={s['handle_to_collar_area_ratio']:.3f} "
              f"edge-length ratio={s['handle_to_collar_mean_edge_length_ratio']:.3f}")

    out = {
        "description": "Gradient-based (L-BFGS-B, exact analytic subgradients) search for "
                       "minimal-area piecewise-flat fillings of S^1 (length 2*pi), genus "
                       "0-2: Heron area + triangle log barrier + penalties on boundary "
                       "cone angles < pi and on k = 5 Steiner distances below d_S1, with "
                       "penalty continuation 1e2 -> 1e3 -> 1e4, feasibility polishing and "
                       "k = 16 + corner-cut certification.",
        "config": {**cfg, "stages": list(STAGES), "eps_length": EPS_LEN,
                   "barrier": BARRIER, "barrier_delta": BARRIER_DELTA},
        "reference": {"pi": np.pi, "two_pi": TWO_PI},
        "best_strictly_feasible": best,
        "runs": runs,
        "total_seconds": round(time.time() - t0, 2),
    }
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).write_text(json.dumps(out, indent=2) + "\n")
    print(f"\nSaved {args.out} ({out['total_seconds']} s)")


if __name__ == "__main__":
    main()

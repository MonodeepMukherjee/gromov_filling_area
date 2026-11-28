"""High-resolution genus 0-2 convergence run of the exact-subgradient filling search.

Same engine as ``discover_extremal_metrics.py`` (L-BFGS-B with analytic gradients of Heron
area, triangle barrier, boundary cone angles and k = 5 Steiner-distance subgradients;
penalty continuation 1e2 -> 1e3 -> 1e4; rescale/blend feasibility polishing), at a finer
boundary (``--n-boundary 24`` by default), with more restarts and a larger budget, and with
certification on the k = 24 Steiner graph plus the exact corner-cut lower bound.

Every objective evaluation is cheap to log, so the script records a convergence curve
(evaluation count, area, penalized objective) for every stage of every restart.

Areas are Riemannian (Heron) areas; the round hemisphere has area 2 pi. A Steiner graph only
upper-bounds intrinsic distance, so certification is strong numerical evidence, not a proof.

Usage:  .venv/bin/python3 scripts/overnight_genus_convergence.py --n-boundary 24 --restarts 8
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

sys.path.insert(0, str(Path(__file__).resolve().parent))
from discover_extremal_metrics import STAGES, GradFillingProblem, structure  # noqa: E402
from explore_genus2 import TWO_PI, build_mesh, heron_area_grad  # noqa: E402


class LoggingProblem(GradFillingProblem):
    """Records (evaluation, area, objective) every ``every`` objective evaluations."""

    def __init__(self, *a, every: int = 250, **kw):
        super().__init__(*a, **kw)
        self.every, self.curve, self.total_evals, self.weight = every, [], 0, None

    def objective_grad(self, x, weight):
        val, grad = super().objective_grad(x, weight)
        self.total_evals += 1
        if self.total_evals % self.every == 0:
            area = heron_area_grad(self.lengths(x), self.mesh.face_edges)[0]
            self.curve.append([self.total_evals, float(weight), float(area), float(val)])
        return val, grad


def run_restart(genus: int, restart: int, cfg: dict) -> dict:
    t_all = time.time()
    mesh = build_mesh(genus, n_b=cfg["n_boundary"])
    prob = LoggingProblem(mesh, cfg["steiner_k"], cfg["certify_k"], cfg["angle_margin"],
                          every=cfg["log_every"])
    tol = cfg["strict_tol"]
    seed = None if restart == 0 else 7000 * (genus + 1) + restart
    rng = None if seed is None else np.random.default_rng(seed)
    tag = f"g={genus} r={restart}"

    t0 = time.time()
    x0, c0 = prob.feasible_start(tol, rng, jitter=cfg["jitter"])
    start = {"hemisphere_scale_c": c0, "seconds": round(time.time() - t0, 1)}
    start.update(prob.certify(x0, tol))
    print(f"  [{tag} start ] A={start['area']:.4f} ({start['seconds']} s)", flush=True)

    x, stages = x0, []
    for w in STAGES:
        x, info = prob.run_stage(x, w, cfg["maxiter"], max_cycles=cfg["max_cycles"])
        stages.append(info)
        print(f"  [{tag} w={w:.0e}] A={info['area']:.4f} "
              f"k{prob.steiner_k}={info[f'k{prob.steiner_k}_violation']:.1e} "
              f"nit={info['nit']} cycles={info['lbfgsb_cycles']} ({info['seconds']} s)",
              flush=True)

    t0 = time.time()
    x_fin, how = prob.restore(x, x0, tol)
    final = {**how, "seconds": round(time.time() - t0, 1)}
    final.update(prob.certify(x_fin, tol))
    final["structure"] = structure(mesh, prob.lengths(x_fin))
    print(f"  [{tag} final ] A={final['area']:.4f} A/2pi={final['area_over_2pi']:.4f} "
          f"k{prob.certify_k}={final['k16_violation']:.1e} lb={final['exact_lower_bound']:.1e} "
          f"strict={final['strictly_feasible']} ({round(time.time() - t_all)} s)", flush=True)
    return {"genus": genus, "restart": restart, "seed": seed, "mesh": mesh.info,
            "free_edges": int(prob.free.sum()), "feasible_start": start, "stages": stages,
            "final": final, "curve": prob.curve, "final_edge_lengths":
            prob.lengths(x_fin).tolist(), "seconds": round(time.time() - t_all, 1)}


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--n-boundary", type=int, default=24)
    ap.add_argument("--restarts", type=int, default=8)
    ap.add_argument("--genera", type=int, nargs="+", default=[0, 1, 2])
    ap.add_argument("--maxiter", type=int, default=10000, help="L-BFGS-B iterations per stage")
    ap.add_argument("--max-cycles", type=int, default=60)
    ap.add_argument("--jitter", type=float, default=0.25)
    ap.add_argument("--angle-margin", type=float, default=1e-3)
    ap.add_argument("--strict-tol", type=float, default=1e-10)
    ap.add_argument("--steiner-k", type=int, default=5)
    ap.add_argument("--certify-k", type=int, default=24)
    ap.add_argument("--log-every", type=int, default=250)
    ap.add_argument("--workers", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--out", default="benchmarks/overnight_convergence.json")
    args = ap.parse_args()
    cfg = vars(args)

    t0 = time.time()
    jobs = [(g, r) for g in sorted(args.genera, reverse=True) for r in range(args.restarts)]
    print(f"{len(jobs)} jobs on {args.workers} workers", flush=True)
    runs = []
    with ProcessPoolExecutor(max_workers=args.workers) as ex:
        futs = [ex.submit(run_restart, g, r, cfg) for g, r in jobs]
        for fut in as_completed(futs):
            runs.append(fut.result())
            partial = {"partial": True, "config": cfg, "runs": sorted(
                runs, key=lambda r: (r["genus"], r["restart"]))}
            Path(args.out).write_text(json.dumps(partial) + "\n")
    runs.sort(key=lambda r: (r["genus"], r["restart"]))

    summary = {}
    for g in args.genera:
        mine = [r for r in runs if r["genus"] == g]
        ok = [r for r in mine if r["final"]["strictly_feasible"]]
        areas = sorted(r["final"]["area"] for r in ok)
        best = min(ok, key=lambda r: r["final"]["area"]) if ok else None
        summary[str(g)] = {
            "restarts": len(mine), "strictly_feasible": len(ok),
            "best_area": areas[0] if ok else None,
            "best_area_over_2pi": areas[0] / TWO_PI if ok else None,
            "best_restart": best["restart"] if best else None,
            "median_area": float(np.median(areas)) if ok else None,
            "areas": areas,
            "best_penalized_area_before_polish": min(r["stages"][-1]["area"] for r in mine),
            "best_structure": best["final"]["structure"] if best else None,
        }
        s = summary[str(g)]
        if ok:
            print(f"genus {g}: {len(ok)}/{len(mine)} strictly feasible, best A="
                  f"{s['best_area']:.5f} (A/2pi={s['best_area_over_2pi']:.5f}), median "
                  f"{s['median_area']:.4f}; best penalized {s['best_penalized_area_before_polish']:.4f}")
    out = {
        "description": __doc__.split("\n\n")[0],
        "config": cfg | {"stages": list(STAGES)},
        "reference": {"two_pi": TWO_PI},
        "summary": summary,
        "runs": runs,
        "total_seconds": round(time.time() - t0, 1),
    }
    Path(args.out).write_text(json.dumps(out, indent=1) + "\n")
    print(f"\nSaved {args.out} ({out['total_seconds']} s)")


if __name__ == "__main__":
    main()

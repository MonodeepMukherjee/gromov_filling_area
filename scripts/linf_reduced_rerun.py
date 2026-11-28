"""Re-optimize the even-n configurations of ``linf_multi_point_search.py`` in reduced form.

For even n the equidistant anchors come in antipodal pairs, and d(t, a + pi) = pi - d(t, a),
so gamma_n is isometric (in the sup norm) to gamma on the n/2 anchors k pi/(n/2). In the
redundant n-dimensional form every sup-norm maximum is a permanent tie, and L-BFGS-B stops
after 0-6 iterations, leaving the hemisphere image unimproved. This script reruns n = 6, 8,
12, 16 in reduced form (same boundary breaks, hence the same meshes), merges the results
into ``benchmarks/linf_multi_point.json`` and recomputes the effective-dimension fits.
"""

from __future__ import annotations

import json
import sys
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from linf_multi_point_search import boundary_breaks, disk_job  # noqa: E402

OUT = Path("benchmarks/linf_multi_point.json")


def main():
    d = json.loads(OUT.read_text())
    levels = d["config"]["levels"]
    maxiter = d["config"]["maxiter"]
    ns = [int(a) for a in sys.argv[1:]] or [6, 8, 12, 16]
    reduced = {n: np.pi * np.arange(n // 2) / (n // 2) for n in ns}
    jobs, keys = [], []
    for n, anc in reduced.items():
        for mmin, R in levels:
            s = max(1, int(np.ceil(mmin / len(boundary_breaks(anc)))))
            for start in ("hemisphere", "cone"):
                jobs.append((anc, s, R, maxiter, start))
                keys.append(n)
    order = sorted(range(len(jobs)), key=lambda i: -len(jobs[i][0]) * jobs[i][2])
    with ProcessPoolExecutor() as ex:
        out = list(ex.map(disk_job, [jobs[i] for i in order], chunksize=1))
    runs = {n: [] for n in ns}
    for i, r in zip(order, out):
        runs[keys[i]].append(r)
    for n in ns:
        res = d["results"][str(n)]
        best = [min((r for r in runs[n] if r["R"] == R), key=lambda r: r["min_area"])
                for _, R in levels]
        res["redundant_ceiling_by_level"] = res["ceiling_by_level"]
        res["reduced_anchors"] = reduced[n].tolist()
        res["reduced_runs"] = runs[n]
        res["ceiling_by_level"] = [min(a, r["min_area"]) for a, r in
                                   zip(res["redundant_ceiling_by_level"], best)]
        res["ceiling"] = min(res["ceiling_by_level"])
        print(f"n={n:2d} (m={n // 2}) ceiling by level "
              + " ".join(f"{v:.4f}" for v in res["ceiling_by_level"])
              + f"  (redundant form: {res['redundant_ceiling_by_level'][-1]:.4f})", flush=True)

    eff = {}
    for k, v in d["results"].items():
        n = int(k.split("_")[0])
        m = 2 if n == 2 else (n // 2 if n % 2 == 0 else n)
        eff[m] = min(eff.get(m, np.inf), v["ceiling"])

    def fit(ms, power):
        x = np.array([1 / m**power for m in ms])
        y = np.array([eff[m] for m in ms])
        b, a = np.polyfit(x, y, 1)
        return {"effective_m": ms, "model": f"a + b / m^{power}", "limit": float(a),
                "slope": float(b), "residual_max": float(np.max(np.abs(a + b * x - y)))}

    e = d["extrapolation"]["effective_dimension"]
    e["effective_ceilings"] = {str(m): eff[m] for m in sorted(eff)}
    for key in [k for k in e if k.startswith("fit_")]:
        del e[key]
    e["fits"] = [fit([4, 5, 6, 8], 2), fit([3, 4, 5, 6, 8], 2), fit([4, 5, 6, 8], 1),
                 fit([3, 4, 5, 6, 8], 1)]
    e["reduced_rerun"] = "even n re-optimized in reduced form by scripts/linf_reduced_rerun.py"
    print(json.dumps(e["effective_ceilings"], indent=1))
    for f in e["fits"]:
        print(f)
    OUT.write_text(json.dumps(d, indent=1) + "\n")


if __name__ == "__main__":
    main()

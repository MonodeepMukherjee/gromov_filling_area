"""Angular visibility caps and the pi/2-collar on the best certified fillings, genus 0-2.

For each genus g = 0, 1, 2 this reloads the best k = 48 certified intrinsic edge-length
metric from ``benchmarks/extremal_bound_discovery.json`` and evaluates, at every sample
point x of a fine face quadrature (each face refined into ``M_SUB**2`` sub-triangles):

  * inradius(x) = min_theta d(x, iota theta)   (distance to the boundary circle), and
  * cap_frac(x) = (1 / 2 pi) |{theta : d(x, iota theta) < pi / 2}|  in [0, 1/2],

the discrete counterpart of ``angularCap F x`` in ``IncidenceFubini.lean``. The collar is
U = {inradius < pi / 2}; outside it the cap is empty.

Boundary circle. The boundary edges have length 2 pi / n_b. The theta samples are the
n_b boundary vertices plus every ``THETA_STRIDE``-th Steiner point of the boundary edges,
which are uniformly spaced in arclength, so each sample carries weight 1 / n_theta.

Distance field. As in ``search_genus2_invariant.py``: Dijkstra on the Steiner graph
(``K`` points per edge), then inside each flat unfolded face
d(theta, x) = min over the face's boundary nodes q of d(theta, q) + |q - x|. For speed
only the corners and every ``Q_STRIDE``-th Steiner node of each face edge are used as q,
which can only overestimate d, so ball areas and caps are slightly low.

Pruning. Dijkstra stops at pi/2 plus the largest sub-triangle diameter; beyond that
distances are clamped. This leaves every cap, ball area and the collar area exact, but
the reported maximum inradius is capped at that limit.

Incidence integral. For each theta the area of {d(theta, .) < pi / 2} is computed exactly
on the piecewise-linear field (``sublevel_area``). Averaging over theta gives
mean_theta Area(B(iota theta, pi / 2)). By Tonelli (``lintegral_boundaryBall_eq_
lintegral_angularCap``) this equals the integral over M of cap_frac. The PL sublevel
formula is the one of ``sublevel_area`` in ``search_genus2_invariant.py``. A pointwise
quadrature of cap_frac over the sub-triangles is reported as a cross-check.

Run:  .venv/bin/python3 scripts/analyze_angular_caps.py
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

import numpy as np
from scipy.sparse.csgraph import dijkstra

sys.path.insert(0, str(Path(__file__).resolve().parent))
from explore_genus2 import PathDistance, build_mesh, heron_area_grad  # noqa: E402
from search_genus2_invariant import (  # noqa: E402
    best_runs, face_layout, face_nodes, sub_lattice, weighted_graph)

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "benchmarks" / "extremal_bound_discovery.json"
INV = ROOT / "benchmarks" / "genus2_invariant_search.json"
OUT = ROOT / "benchmarks" / "angular_cap_analysis.json"
N_B = 24
K = 23  # Steiner points per edge: fractions j / 24 along each edge
THETA_STRIDE = 2  # theta samples: boundary vertices + Steiner points j = 2, 4, ..., 22
Q_STRIDE = 2  # face fields use the corners + every 2nd Steiner node of each face edge
M_SUB = 16
R = np.pi / 2


def theta_sources(mesh) -> tuple[np.ndarray, np.ndarray]:
    """Uniform boundary samples (graph node ids) and a mask of the boundary vertices."""
    bnd = list(mesh.boundary)
    vid = {v: i for i, v in enumerate(bnd)}
    ids, is_vertex = [], []
    for ek in np.flatnonzero(mesh.bnd_edge_mask):
        u, w = mesh.edges[ek]
        # orient the edge along the boundary cycle so samples are ordered (not required)
        if (vid[int(w)] - vid[int(u)]) % N_B != 1:
            u, w = w, u
        ids.append(int(u))
        is_vertex.append(True)
        for j in range(THETA_STRIDE, K + 1, THETA_STRIDE):
            ids.append(mesh.n_vertices + int(ek) * K + (j - 1))
            is_vertex.append(False)
    return np.array(ids), np.array(is_vertex)


def sublevel_at(vals: np.ndarray, area: np.ndarray, t: float) -> np.ndarray:
    """Exact area of {PL field < t} per source; vals (S, T, 3), area (T,).

    Same formula as ``sublevel_area`` in ``search_genus2_invariant.py``, evaluated only on
    sub-triangles that cross the level t (the others contribute 0 or their full area).
    """
    full = (vals.max(axis=-1) < t) @ area
    si, ti = np.nonzero((vals.min(axis=-1) < t) & (vals.max(axis=-1) >= t))
    v = np.sort(vals[si, ti].astype(np.float64), axis=-1)
    v0, v1, v2 = v[:, 0], v[:, 1], v[:, 2]
    d20 = np.maximum(v2 - v0, 1e-300)
    lo = (t - v0) ** 2 / np.maximum((v1 - v0) * d20, 1e-300)
    hi = 1.0 - (v2 - t) ** 2 / np.maximum((v2 - v1) * d20, 1e-300)
    frac = np.clip(np.where(t <= v1, lo, hi), 0.0, 1.0)
    return full + np.bincount(si, weights=frac * area[ti], minlength=len(vals))


def analyse(genus: int, run: dict, inv: dict) -> dict:
    t0 = time.time()
    mesh = build_mesh(genus, n_b=N_B)
    lengths = np.array(run["final_edge_lengths"])
    assert len(lengths) == len(mesh.edges), "mesh does not match stored edge vector"
    area = float(heron_area_grad(lengths, mesh.face_edges)[0])
    bl = lengths[mesh.bnd_edge_mask]
    assert np.allclose(bl, 2 * np.pi / N_B), "boundary edges are not uniform"

    pd = PathDistance(mesh, K)
    g = weighted_graph(pd, lengths)
    src, is_vertex = theta_sources(mesh)
    n_theta = len(src)
    # Only d < pi/2 + (sub-triangle diameter) can affect a cap, a ball or the collar: the
    # face field is 1-Lipschitz, so every corner of a sub-triangle crossing pi/2 is below
    # this limit, and so is its minimizing node q. Farther nodes are pruned (set to ``far``).
    limit = R + lengths.max() / M_SUB + 1e-6
    far = np.float32(limit + 1.0)
    d_src = dijkstra(g, directed=True, indices=src, limit=limit)
    d_src = np.minimum(d_src, far).astype(np.float32)  # (S, nodes)

    P = face_layout(lengths, mesh.face_edges)
    ids, bws = face_nodes(mesh, K)
    keep = np.r_[0:3, 3 + np.flatnonzero((np.arange(3 * K) % K) % Q_STRIDE == Q_STRIDE - 1)]
    ids, bws = ids[:, keep], bws[:, keep]
    node_xy = np.einsum("fqs,fsd->fqd", bws, P)
    lat_bw, tris = sub_lattice(M_SUB)
    lat_xy = np.einsum("ps,fsd->fpd", lat_bw, P)
    eu = np.linalg.norm(lat_xy[:, :, None, :] - node_xy[:, None, :, :],
                        axis=-1).astype(np.float32)  # (F, Pl, Q)
    xy = lat_xy[:, tris, :].reshape(-1, 3, 2)

    e1, e2 = xy[:, 1] - xy[:, 0], xy[:, 2] - xy[:, 0]
    sub_area = 0.5 * np.abs(e1[:, 0] * e2[:, 1] - e1[:, 1] * e2[:, 0])

    # d(theta, x) at every lattice point: running min over the face boundary nodes q
    dq = np.ascontiguousarray(np.moveaxis(d_src[:, ids], -1, 0))  # (Q, S, F)
    eq = np.ascontiguousarray(np.moveaxis(eu, -1, 0))  # (Q, F, Pl)
    field = dq[0][:, :, None] + eq[0][None]  # (S, F, Pl)
    tmp = np.empty_like(field)
    for q in range(1, len(dq)):
        np.add(dq[q][:, :, None], eq[q][None], out=tmp)
        np.minimum(field, tmp, out=field)

    cap = (field < R).mean(axis=0)  # cap_frac at lattice points
    inrad = field.min(axis=0)
    ball = sublevel_at(field[:, :, tris].reshape(n_theta, -1, 3), sub_area, R)
    # collar area: exact PL sublevel area of the inradius field
    collar_area = float(sublevel_at(inrad[None, :, tris].reshape(1, -1, 3), sub_area, R)[0])
    # pointwise quadrature cross-check: corner average of cap_frac on each sub-triangle
    cap_quad = float((cap[:, tris].reshape(-1, 3).mean(axis=1) * sub_area).sum())

    incidence = float(ball.mean())  # mean_theta Area(B(iota theta, pi/2)) = int cap_frac
    inv_res = inv["results"][str(genus)]["integral_0_halfpi"]
    vertex_mean = float(ball[is_vertex].mean())
    res = {
        "genus": genus,
        "restart": run["restart"],
        "area": area,
        "area_over_2pi": area / (2 * np.pi),
        "n_theta": int(n_theta),
        "collar_area": collar_area,
        "collar_area_fraction": collar_area / area,
        "core_area": area - collar_area,
        "max_inradius_capped": float(min(inrad.max(), limit)),
        "inradius_cap": float(limit),
        "mean_cap_frac_in_collar": incidence / collar_area,
        "mean_cap_frac_over_M": incidence / area,
        "max_cap_frac": float(cap.max()),
        "incidence_integral": incidence,
        "incidence_integral_pointwise_quadrature": cap_quad,
        "incidence_over_area": incidence / area,
        "hemisphere_incidence": float(np.pi),
        "ball_area_min": float(ball.min()),
        "ball_area_max": float(ball.max()),
        "ball_area_mean_vertex_anchors": vertex_mean,
        "invariant_search_mean_ball_area": inv_res["mean_profile"],
        "rel_diff_vertex_anchors_vs_invariant_search":
            (vertex_mean - inv_res["mean_profile"]) / inv_res["mean_profile"],
        "seconds": round(time.time() - t0, 2),
    }
    return res


def main() -> None:
    t_all = time.time()
    best = best_runs(json.loads(SRC.read_text()))
    inv = json.loads(INV.read_text())
    results = {}
    for g in (0, 1, 2):
        r = analyse(g, best[g], inv)
        results[str(g)] = r
        print(f"g={g} A/2pi={r['area_over_2pi']:.4f} collar={r['collar_area_fraction']:.4f} "
              f"mean_cap|U={r['mean_cap_frac_in_collar']:.4f} max_cap={r['max_cap_frac']:.4f} "
              f"int_cap={r['incidence_integral']:.4f} "
              f"(quad {r['incidence_integral_pointwise_quadrature']:.4f},"
              f" inv {r['invariant_search_mean_ball_area']:.4f}, pi={np.pi:.4f}) "
              f"{r['seconds']}s", flush=True)
    out = {
        "description": ("Angular visibility caps cap_frac(x) and the pi/2-collar "
                        "{inradius < pi/2} on the best k = 48 certified discrete fillings "
                        "(genus 0-2, n_b = 24)."),
        "units": "Riemannian (boundary length 2 pi); multiply areas by 4/pi for mu_H[2]",
        "config": {"source": str(SRC.relative_to(ROOT)), "n_boundary": N_B,
                   "steiner_k": K, "theta_stride": THETA_STRIDE, "q_stride": Q_STRIDE,
                   "face_refinement": M_SUB},
        "results": results,
        "total_seconds": round(time.time() - t_all, 2),
    }
    OUT.write_text(json.dumps(out, indent=1) + "\n")
    print(f"wrote {OUT.relative_to(ROOT)} in {out['total_seconds']}s")


if __name__ == "__main__":
    main()

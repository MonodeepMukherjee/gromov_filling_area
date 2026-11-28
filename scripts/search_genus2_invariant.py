"""Distance-sphere slice profiles on the best certified discrete fillings, genus 0-2.

For each genus g = 0, 1, 2 this loads the best k = 48 certified intrinsic edge-length
metric stored in ``benchmarks/extremal_bound_discovery.json`` (``final_edge_lengths``)
on the ``build_mesh(g, n_b=24)`` triangulation, and measures the level sets

    L_g(t; b) = length({x in M : d_int(x, b) = t})

of the intrinsic distance from each boundary vertex b = b_0 .. b_23.

Distance field. ``d_int(b, .)`` is computed at every vertex and Steiner point
(``K`` points per edge) by Dijkstra on the same Steiner graph as ``PathDistance``.
Each face is unfolded in the plane and refined into ``M_SUB**2`` sub-triangles.
At a lattice point x of a face, d(b, x) = min over the face's boundary nodes q of
d(b, q) + |q - x|; this holds because geodesics are straight inside a flat face. The
field is then interpolated linearly on each sub-triangle, and the level set
{d = t} is a union of straight segments whose lengths are summed exactly.

Benchmarks (Riemannian units, boundary length 2 pi):
  * ``2 pi sin t``: the distance circle around the *pole* of the unit hemisphere.
  * ``pi sin t``: the distance sphere around a *boundary* point of the hemisphere,
    which is a half-circle. This is the benchmark matching boundary anchors b_i.
  * ``pi t``: the linear planar profile (pi^2 / 2) * t / (pi / 2).

Coarea check: since |grad d| = 1 a.e., the integral of L(t; b) over the full range
[0, max d] equals the area. Its integral over [0, pi / 2] is the area of the
ball B(b, pi / 2), which on the hemisphere is pi (not 2 pi) for a boundary anchor.
An interior "centre" anchor (the point farthest from the boundary, among vertices) is
also reported, because 2 pi sin t is the right comparison for that anchor.

Run:  .venv/bin/python3 scripts/search_genus2_invariant.py
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

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "benchmarks" / "extremal_bound_discovery.json"
OUT = ROOT / "benchmarks" / "genus2_invariant_search.json"
N_B = 24
K = 24  # Steiner points per edge (the certification resolution of the request)
M_SUB = 4  # each face is refined into M_SUB**2 sub-triangles
T_GRID = np.linspace(0.05, np.pi / 2 - 0.02, 20)
N_FINE = 401  # fine grid for the integrals


def best_runs(data: dict) -> dict[int, dict]:
    best: dict[int, dict] = {}
    for r in data["metric"]["runs"]:
        f = r["final"]
        if not (f["certified"] and f["strictly_feasible"]):
            continue
        g = r["genus"]
        if g not in best or f["area"] < best[g]["final"]["area"]:
            best[g] = r
    return best


def face_layout(lengths: np.ndarray, face_edges: np.ndarray) -> np.ndarray:
    """Planar corners (F, 3, 2): A = (0, 0), B = (|AB|, 0), C = (x, y)."""
    la, lb, lc = (lengths[face_edges[:, s]] for s in range(3))
    x = (lb * lb + lc * lc - la * la) / (2 * lc)
    y = np.sqrt(np.maximum(lb * lb - x * x, 0.0))
    P = np.zeros((len(la), 3, 2))
    P[:, 1, 0] = lc
    P[:, 2, 0], P[:, 2, 1] = x, y
    return P


def face_nodes(mesh, k: int) -> tuple[np.ndarray, np.ndarray]:
    """Per face: the 3 + 3k graph-node ids on its boundary and their barycentrics."""
    V = mesh.n_vertices
    ts = np.arange(1, k + 1) / (k + 1)
    ids, bws = [], []
    for fi, verts in enumerate(mesh.faces.tolist()):
        nid, bw = list(verts), [np.eye(3)[s] for s in range(3)]
        for slot, (p, q) in enumerate(((1, 2), (2, 0), (0, 1))):
            ek = mesh.face_edges[fi, slot]
            u = mesh.edges[ek][0]
            pu, pv = (p, q) if verts[p] == u else (q, p)
            for t_i, t in enumerate(ts):
                w = np.zeros(3)
                w[pu], w[pv] = 1.0 - t, t
                nid.append(V + ek * k + t_i)
                bw.append(w)
        ids.append(nid)
        bws.append(bw)
    return np.array(ids), np.array(bws)


def sub_lattice(m: int) -> tuple[np.ndarray, np.ndarray]:
    """Barycentric lattice points of a face and the (m**2, 3) sub-triangle index list."""
    pts, index = [], {}
    for i in range(m + 1):
        for j in range(m + 1 - i):
            index[(i, j)] = len(pts)
            pts.append([(m - i - j) / m, i / m, j / m])
    tris = []
    for i in range(m):
        for j in range(m - i):
            tris.append([index[(i, j)], index[(i + 1, j)], index[(i, j + 1)]])
            if i + j < m - 1:
                tris.append([index[(i + 1, j)], index[(i + 1, j + 1)], index[(i, j + 1)]])
    return np.array(pts), np.array(tris)


def weighted_graph(pd: PathDistance, lengths: np.ndarray):
    """The Steiner graph of ``pd`` with face-unfolded Euclidean weights."""
    fe = pd.mesh.face_edges
    lengths = np.maximum(lengths, 1e-9)
    la, lb, lc = (lengths[fe[:, s]] for s in range(3))
    x = (lb * lb + lc * lc - la * la) / (2 * lc)
    y = np.sqrt(np.maximum(lb * lb - x * x, 0.0))
    f = pd.faces_of
    d1, d2 = pd.dw[:, 1], pd.dw[:, 2]
    w = np.maximum(np.hypot(d1 * lc[f] + d2 * x[f], d2 * y[f]), 1e-12)
    g = pd.graph.copy()
    g.data = w[pd.order]
    return g


def lattice_field(dist_nodes: np.ndarray, ids: np.ndarray, node_xy: np.ndarray,
                  lat_xy: np.ndarray) -> np.ndarray:
    """d at lattice points (S, F, P): min over face boundary nodes of d(q) + |q - x|."""
    # node_xy (F, Q, 2), lat_xy (F, P, 2) -> euclidean (F, P, Q)
    eu = np.linalg.norm(lat_xy[:, :, None, :] - node_xy[:, None, :, :], axis=-1)
    dq = dist_nodes[:, ids]  # (S, F, Q)
    return np.min(dq[:, :, None, :] + eu[None], axis=-1)


def sorted_corners(vals: np.ndarray, xy: np.ndarray):
    """Sort each sub-triangle's corner values; return v0 <= v1 <= v2, mid-level length, area.

    vals (S, T3, 3), xy (T3, 3, 2). In a linear triangle the level set {f = t} is a
    segment whose length is a tent in t: 0 at v0, ``lmid`` at v1, 0 at v2.
    """
    order = np.argsort(vals, axis=-1)
    v = np.take_along_axis(vals, order, axis=-1)
    pts = xy[None].repeat(vals.shape[0], axis=0)
    pts = np.take_along_axis(pts, order[..., None], axis=-2)
    span = v[..., 2] - v[..., 0]
    lam = np.where(span > 0, (v[..., 1] - v[..., 0]) / np.where(span > 0, span, 1.0), 0.0)
    q = pts[..., 0, :] + lam[..., None] * (pts[..., 2, :] - pts[..., 0, :])
    lmid = np.linalg.norm(q - pts[..., 1, :], axis=-1)
    e1, e2 = xy[:, 1] - xy[:, 0], xy[:, 2] - xy[:, 0]
    area = 0.5 * np.abs(e1[:, 0] * e2[:, 1] - e1[:, 1] * e2[:, 0])
    return v, lmid, area


def pl_level_length(v, lmid, t: float) -> np.ndarray:
    """Exact level-set length of the PL field at level t, per source (S,)."""
    v0, v1, v2 = v[..., 0], v[..., 1], v[..., 2]
    up = np.where((v0 < t) & (t <= v1) & (v1 > v0), (t - v0) / np.where(v1 > v0, v1 - v0, 1), 0)
    dn = np.where((v1 < t) & (t < v2) & (v2 > v1), (v2 - t) / np.where(v2 > v1, v2 - v1, 1), 0)
    return (lmid * (up + dn)).sum(axis=-1)


def sublevel_area(v, area, t: float) -> np.ndarray:
    """Exact area of {PL field < t}, per source (S,)."""
    v0, v1, v2 = v[..., 0], v[..., 1], v[..., 2]
    d20 = np.maximum(v2 - v0, 1e-300)
    lo = (t - v0) ** 2 / np.maximum((v1 - v0) * d20, 1e-300)
    hi = 1.0 - (v2 - t) ** 2 / np.maximum((v2 - v1) * d20, 1e-300)
    frac = np.where(t <= v0, 0.0, np.where(t >= v2, 1.0, np.where(t <= v1, lo, hi)))
    return (area * np.clip(frac, 0.0, 1.0)).sum(axis=-1)


def analyse(genus: int, run: dict) -> dict:
    t0 = time.time()
    mesh = build_mesh(genus, n_b=N_B)
    lengths = np.array(run["final_edge_lengths"])
    assert len(lengths) == len(mesh.edges), "mesh does not match stored edge vector"
    area = heron_area_grad(lengths, mesh.face_edges)[0]

    pd = PathDistance(mesh, K)
    g = weighted_graph(pd, lengths)
    bnd = np.array(mesh.boundary)
    d_b = dijkstra(g, directed=True, indices=bnd)  # (24, n_nodes)

    # Distance to the boundary curve (vertices + boundary-edge Steiner points).
    bnd_edges = np.flatnonzero(mesh.bnd_edge_mask)
    bnd_nodes = np.concatenate([bnd, (mesh.n_vertices + bnd_edges[:, None] * K
                                      + np.arange(K)[None]).ravel()])
    d_to_bnd = dijkstra(g, directed=True, indices=bnd_nodes, min_only=True)
    interior = np.setdiff1d(np.arange(mesh.n_vertices), bnd)
    centre = int(interior[np.argmax(d_to_bnd[interior])])
    d_c = dijkstra(g, directed=True, indices=[centre])
    sources = np.vstack([d_b, d_c])  # last row = centre anchor

    P = face_layout(lengths, mesh.face_edges)  # (F, 3, 2)
    ids, bws = face_nodes(mesh, K)
    node_xy = np.einsum("fqs,fsd->fqd", bws, P)
    lat_bw, tris = sub_lattice(M_SUB)
    lat_xy = np.einsum("ps,fsd->fpd", lat_bw, P)
    field = lattice_field(sources, ids, node_xy, lat_xy)  # (S, F, Pl)

    vals = field[:, :, tris].reshape(len(sources), -1, 3)  # (S, F * m^2, 3)
    xy = lat_xy[:, tris, :].reshape(-1, 3, 2)

    v, lmid, sub_area = sorted_corners(vals, xy)
    t_max = float(field.max())

    # Primary profile: coarea-consistent L(t) = dA/dt, with A(t) = area{d < t}.
    t_half = np.linspace(0.0, np.pi / 2, N_FINE)
    A_half = np.stack([sublevel_area(v, sub_area, t) for t in t_half], axis=1)  # (S, N)
    dA = np.diff(A_half, axis=1)  # area of each shell {t_k <= d < t_k+1}
    h = 1e-2
    L_grid = np.stack([(sublevel_area(v, sub_area, t + h) - sublevel_area(v, sub_area, t - h))
                       / (2 * h) for t in T_GRID], axis=1)
    # Cross-check: direct PL level-set length (biased low where the field kinks).
    L_pl = np.stack([pl_level_length(v, lmid, t) for t in T_GRID], axis=1)
    pl_full = (lmid * (v[..., 2] - v[..., 0]) / 2).sum(axis=-1)  # exact int of tents

    Lb_grid, Lc_grid = L_grid[:-1], L_grid[-1]
    int_min = float(dA[:-1].min(axis=0).sum())
    int_mean = float(dA[:-1].mean(axis=0).sum())
    int_per_anchor = A_half[:-1, -1]
    int_centre = float(A_half[-1, -1])
    Lpl_b = L_pl[:-1]

    ref_pole = 2 * np.pi * np.sin(T_GRID)
    ref_bnd = np.pi * np.sin(T_GRID)
    ref_lin = np.pi * T_GRID
    min_prof, mean_prof = Lb_grid.min(axis=0), Lb_grid.mean(axis=0)
    res = {
        "genus": genus,
        "restart": run["restart"],
        "area": float(area),
        "area_over_2pi": float(area / (2 * np.pi)),
        "stored_area": run["final"]["area"],
        "certify_k_stored": run["final"]["certify_k"],
        "mesh": run["mesh"],
        "t_grid": T_GRID.tolist(),
        "min_profile": min_prof.tolist(),
        "mean_profile": mean_prof.tolist(),
        "argmin_anchor": Lb_grid.argmin(axis=0).tolist(),
        "centre_profile": Lc_grid.tolist(),
        "ref_2pi_sin_t": ref_pole.tolist(),
        "ref_pi_sin_t_boundary": ref_bnd.tolist(),
        "ref_pi_t_linear": ref_lin.tolist(),
        "min_over_pi_sin_t": (min_prof / ref_bnd).tolist(),
        "mean_over_pi_sin_t": (mean_prof / ref_bnd).tolist(),
        "min_over_pi_t": (min_prof / ref_lin).tolist(),
        "min_ge_pi_t_everywhere": bool(np.all(min_prof >= ref_lin)),
        "min_ge_pi_sin_t_everywhere": bool(np.all(min_prof >= ref_bnd)),
        "integral_0_halfpi": {
            "min_profile": int_min,
            "mean_profile": int_mean,
            "per_anchor_min": float(int_per_anchor.min()),
            "per_anchor_max": float(int_per_anchor.max()),
            "centre_anchor": int_centre,
            "hemisphere_boundary_anchor": float(np.pi),
            "hemisphere_pole": float(2 * np.pi),
            "pi_t_linear": float(np.pi ** 3 / 8),
            "min_gt_2pi": int_min > 2 * np.pi,
            "mean_gt_2pi": int_mean > 2 * np.pi,
            "centre_gt_2pi": int_centre > 2 * np.pi,
        },
        "pl_level_set_crosscheck": {
            "min_profile": Lpl_b.min(axis=0).tolist(),
            "mean_profile": Lpl_b.mean(axis=0).tolist(),
            "centre_profile": L_pl[-1].tolist(),
            "full_range_integral_over_area_min": float((pl_full / area).min()),
            "full_range_integral_over_area_max": float((pl_full / area).max()),
            "mean_ratio_pl_to_dAdt": float(np.mean(L_pl[:, 1:] / L_grid[:, 1:])),
        },
        "max_distance": t_max,
        "centre_vertex": centre,
        "centre_dist_to_boundary": float(d_to_bnd[centre]),
        "seconds": round(time.time() - t0, 2),
    }
    return res


def main() -> None:
    t_all = time.time()
    data = json.loads(SRC.read_text())
    best = best_runs(data)
    results = {}
    for g in (0, 1, 2):
        r = analyse(g, best[g])
        results[str(g)] = r
        i = r["integral_0_halfpi"]
        c = r["pl_level_set_crosscheck"]
        print(f"g={g} r={r['restart']} A/2pi={r['area_over_2pi']:.4f} "
              f"int_min={i['min_profile']:.4f} int_mean={i['mean_profile']:.4f} "
              f"int_centre={i['centre_anchor']:.4f} (2pi={2 * np.pi:.4f}) "
              f"PL/area={c['full_range_integral_over_area_min']:.3f} {r['seconds']}s", flush=True)
    out = {
        "description": ("Distance-sphere level-set lengths L_g(t; b_i) on the best k = 48 "
                        "certified discrete fillings (genus 0-2, n_b = 24)."),
        "units": "Riemannian (boundary length 2 pi); multiply areas by 4/pi for mu_H[2]",
        "config": {"source": str(SRC.relative_to(ROOT)), "n_boundary": N_B,
                   "steiner_k": K, "face_refinement": M_SUB, "n_fine": N_FINE},
        "results": results,
        "total_seconds": round(time.time() - t_all, 2),
    }
    OUT.write_text(json.dumps(out, indent=1) + "\n")
    print(f"wrote {OUT.relative_to(ROOT)} in {out['total_seconds']}s")


if __name__ == "__main__":
    main()

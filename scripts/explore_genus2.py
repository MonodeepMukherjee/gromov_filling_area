"""Numerical exploration of discrete fillings of S^1 (length 2*pi), genus 0-2.

Each filling is an orientable simplicial surface of genus g (Euler
characteristic chi = 1 - 2g) with one boundary cycle of n_b vertices. Its
metric is given by *intrinsic edge lengths* (a piecewise-flat Riemannian
metric), not by coordinates in R^2 or R^3, so a triangle's area comes from
Heron's formula.

Mesh. An octahedron (g = 0) or a connected sum of 7-vertex tori (g >= 1) with
one face punched out, one midpoint subdivision, a collar fanning out to an
n_b-ring, and a *second* collar ring of 4-split quads. The second ring puts every
boundary vertex in four faces (valence 5), so its cone angle can exceed pi.

The boundary edges are fixed at length 2*pi / n_b, so the boundary cycle has
length exactly 2*pi. The interior edge lengths are optimized to

    minimize   sum_faces Heron(l_a, l_b, l_c)
    subject to l_a + l_b - l_c >= eps                  (strict triangle ineq.)
               angle(b_i) >= pi                        (boundary cone angles)
               d(b_i, b_j) >= d_{S^1}(b_i, b_j)         (isometric boundary)

d is computed with scipy.sparse.csgraph.shortest_path on a Steiner graph
(k points per edge, straight segments inside each face unfolded in the
plane), which converges to the true intrinsic distance as k grows.

Solver, one job per (genus, restart), run in parallel:

1. Strictly feasible start. Edge lengths ``ell_init`` come from a
   hemisphere-like polar profile (restarts > 0 draw a random depth exponent and
   jitter interior polar angles); the interior lengths ``c * ell_init`` use the
   smallest scale ``c`` (bisection) at which every constraint holds, with the
   k = 16 violation zero up to roundoff.
2. Powell, then adaptive Nelder-Mead, minimize Heron area
   + 1e4 * sum max(0, d_S1 - d_k5)^2 + 1e4 * sum max(0, pi + 1e-3 - angle)^2
   + an extended log barrier on the triangle slacks. Neither needs gradients.
3. Restoration. The cheaper of a radial rescale ``s * x`` and a blend toward
   the start, found by bisection, that satisfies all constraints with the
   k = 16 violation <= ``--strict-tol`` (roundoff).

Certification: k = 16 violation <= 1e-4 and the exact corner-cut lower bound
== 0 (plus triangle slacks and boundary angles >= pi). A Steiner graph only
upper-bounds distance, so a zero k = 16 reading is strong numerical evidence,
not a proof, of feasibility.

Usage:  .venv/bin/python3 scripts/explore_genus2.py --n-boundary 16 \
            --maxiter 2000 --restarts 4
"""

from __future__ import annotations

import argparse
import json
import os
import time
from collections import defaultdict, deque
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np
from scipy.optimize import minimize
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import shortest_path

TWO_PI = 2.0 * np.pi
EPS_TRI = 1e-3  # strict triangle-inequality margin
EPS_LEN = 1e-3  # lower bound on edge lengths
PENALTY = 1e4  # weight of the squared hinge on d_S1 - d_int
BARRIER = 1e-2  # weight of the log barrier on triangle slacks
ANGLE_PENALTY = 1e4  # weight of the squared hinge on pi - (boundary cone angle)
ANGLE_MARGIN = 1e-3  # the angle hinge targets pi + margin
CERT_TOL = 1e-4  # certification threshold on the k = 16 violation


def circle_geodesic_dist(theta1: float, theta2: float) -> float:
    diff = np.abs(theta1 - theta2) % TWO_PI
    return float(min(diff, TWO_PI - diff))


# ---------------------------------------------------------------------------
# Combinatorial surfaces
# ---------------------------------------------------------------------------

Face = tuple[int, int, int]


def orient(faces: list[Face]) -> list[Face]:
    """Re-orient faces coherently (BFS); raise if the surface is non-orientable."""
    edge_faces: dict[frozenset, list[int]] = defaultdict(list)
    for fi, f in enumerate(faces):
        for k in range(3):
            edge_faces[frozenset((f[k], f[(k + 1) % 3]))].append(fi)
    out: list[Face | None] = [None] * len(faces)
    for seed in range(len(faces)):
        if out[seed] is not None:
            continue
        out[seed] = faces[seed]
        queue = deque([seed])
        while queue:
            fi = queue.popleft()
            f = out[fi]
            for k in range(3):
                u, v = f[k], f[(k + 1) % 3]
                for gj in edge_faces[frozenset((u, v))]:
                    if gj == fi:
                        continue
                    g = faces[gj]
                    has_uv = any(g[m] == u and g[(m + 1) % 3] == v for m in range(3))
                    want = (g[0], g[2], g[1]) if has_uv else g
                    if out[gj] is None:
                        out[gj] = want
                        queue.append(gj)
                    else:
                        h = out[gj]
                        if any(h[m] == u and h[(m + 1) % 3] == v for m in range(3)):
                            raise ValueError("surface is not orientable")
    return [f for f in out if f is not None]


def octahedron() -> list[Face]:
    # vertices: 0,1 poles; 2..5 equator
    eq = [2, 3, 4, 5]
    faces = []
    for i in range(4):
        a, b = eq[i], eq[(i + 1) % 4]
        faces += [(0, a, b), (1, b, a)]
    return orient(faces)


def torus7() -> list[Face]:
    """Moebius-Csaszar minimal 7-vertex triangulation of the torus."""
    faces = []
    for i in range(7):
        faces.append((i, (i + 1) % 7, (i + 3) % 7))
        faces.append((i, (i + 3) % 7, (i + 2) % 7))
    return orient(faces)


def connected_sum(fa: list[Face], fb: list[Face]) -> list[Face]:
    """Connected sum of two closed oriented triangulations along one face each."""
    na = 1 + max(max(f) for f in fa)
    a0, a1, a2 = fa[0]
    b0, b1, b2 = fb[0]
    # orientation-reversing identification of the two removed triangles
    vmap = {b0: a0, b1: a2, b2: a1}
    nxt = na
    for v in sorted({v for f in fb for v in f}):
        if v not in vmap:
            vmap[v] = nxt
            nxt += 1
    faces = fa[1:] + [tuple(vmap[v] for v in f) for f in fb[1:]]
    return orient(faces)


def closed_surface(genus: int) -> list[Face]:
    if genus == 0:
        return octahedron()
    surf = torus7()
    for _ in range(genus - 1):
        surf = connected_sum(surf, torus7())
    return surf


def subdivide(faces: list[Face]) -> list[Face]:
    """1-to-4 midpoint subdivision (keeps the complex simplicial and oriented)."""
    nv = 1 + max(max(f) for f in faces)
    mid: dict[frozenset, int] = {}

    def m(u: int, v: int) -> int:
        nonlocal nv
        key = frozenset((u, v))
        if key not in mid:
            mid[key] = nv
            nv += 1
        return mid[key]

    out = []
    for a, b, c in faces:
        ab, bc, ca = m(a, b), m(b, c), m(c, a)
        out += [(a, ab, ca), (ab, b, bc), (ca, bc, c), (ab, bc, ca)]
    return out


def boundary_cycle(faces: list[Face]) -> list[int]:
    """Vertices of the (unique) boundary cycle, in boundary order."""
    directed = set()
    for f in faces:
        for k in range(3):
            directed.add((f[k], f[(k + 1) % 3]))
    bnd = {(u, v) for (u, v) in directed if (v, u) not in directed}
    succ = {v: u for (u, v) in bnd}  # traverse opposite to face orientation
    if not succ:
        return []
    start = next(iter(succ))
    cyc = [start]
    while True:
        nx = succ[cyc[-1]]
        if nx == start:
            break
        cyc.append(nx)
    if len(cyc) != len(bnd):
        raise ValueError("boundary is not a single cycle")
    return cyc


def add_collar(faces: list[Face], n_b: int) -> tuple[list[Face], list[int]]:
    """Attach an annulus from the current boundary m-cycle to a new n_b-cycle (n_b >= m)."""
    w = boundary_cycle(faces)
    m = len(w)
    if n_b < m:
        raise ValueError(f"n_b={n_b} must be at least the boundary length {m}")
    # outer vertices fanned from inner vertex k: start[k] .. start[k+1] (cyclic)
    start = [(k * n_b) // m for k in range(m + 1)]
    nv = 1 + max(max(f) for f in faces)
    o = list(range(nv, nv + n_b))
    new = list(faces)
    for k in range(m):
        for j in range(start[k], start[k + 1]):
            new.append((w[k], o[j], o[(j + 1) % n_b]))
        new.append((w[k], o[start[k + 1] % n_b], w[(k + 1) % m]))
    new = orient(new)
    return new, o


def add_boundary_strip(faces: list[Face]) -> tuple[list[Face], list[int]]:
    """Second collar ring: a strip of 4-split quads outside the current boundary.

    For the boundary cycle ``w_0 .. w_{n-1}`` it adds a new boundary cycle
    ``b_0 .. b_{n-1}`` and quad centres ``p_0 .. p_{n-1}``; quad
    ``(w_j, w_{j+1}, b_{j+1}, b_j)`` is split into four triangles around ``p_j``.
    Every new boundary vertex ``b_j`` then lies in exactly four faces
    (valence 5: ``b_{j-1}, b_{j+1}, p_{j-1}, p_j, w_j``), so its total cone
    angle can exceed ``pi`` and the boundary can be locally geodesic.
    """
    w = boundary_cycle(faces)
    n = len(w)
    nv = 1 + max(max(f) for f in faces)
    b = list(range(nv, nv + n))
    p = list(range(nv + n, nv + 2 * n))
    new = list(faces)
    for j in range(n):
        j1 = (j + 1) % n
        new += [(w[j], w[j1], p[j]), (w[j1], b[j1], p[j]),
                (b[j1], b[j], p[j]), (b[j], w[j], p[j])]
    return orient(new), b


@dataclass
class Mesh:
    genus: int
    faces: np.ndarray  # (F, 3) vertex indices
    edges: np.ndarray  # (E, 2) sorted vertex pairs
    face_edges: np.ndarray  # (F, 3) edge index opposite each face vertex
    boundary: list[int]  # boundary vertices in cyclic order
    bnd_edge_mask: np.ndarray  # (E,) True for boundary-cycle edges
    n_vertices: int
    info: dict = field(default_factory=dict)


def build_mesh(genus: int, n_b: int = 16, levels: int = 1, strip: bool = True) -> Mesh:
    surf = closed_surface(genus)
    surf = surf[1:]  # punch one hole -> one boundary 3-cycle
    for _ in range(levels):
        surf = subdivide(surf)
    surf, bnd = add_collar(surf, n_b)
    if strip:  # second collar ring: >= 4 faces at every boundary vertex
        surf, bnd = add_boundary_strip(surf)

    # relabel vertices contiguously
    verts = sorted({v for f in surf for v in f})
    relabel = {v: i for i, v in enumerate(verts)}
    faces = np.array([[relabel[v] for v in f] for f in surf], dtype=int)
    bnd = [relabel[v] for v in bnd]
    nv = len(verts)

    eidx: dict[tuple[int, int], int] = {}
    face_edges = np.zeros_like(faces)
    for fi, (a, b, c) in enumerate(faces):
        for slot, (u, v) in enumerate(((b, c), (c, a), (a, b))):  # opposite a, b, c
            key = (min(u, v), max(u, v))
            if key not in eidx:
                eidx[key] = len(eidx)
            face_edges[fi, slot] = eidx[key]
    edges = np.array(sorted(eidx, key=eidx.get), dtype=int)

    bset = set(bnd)
    bnd_pairs = {
        (min(bnd[i], bnd[(i + 1) % n_b]), max(bnd[i], bnd[(i + 1) % n_b])) for i in range(n_b)
    }
    bnd_edge_mask = np.array([tuple(e) in bnd_pairs for e in edges])

    mesh = Mesh(genus, faces, edges, face_edges, bnd, bnd_edge_mask, nv)
    validate(mesh, bset)
    return mesh


def validate(mesh: Mesh, bset: set[int]) -> None:
    """Check simplicial, orientable, manifold, chi = 1 - 2g, one boundary cycle."""
    faces, edges = mesh.faces, mesh.edges
    V, E, F = mesh.n_vertices, len(edges), len(faces)
    chi = V - E + F
    assert chi == 1 - 2 * mesh.genus, f"chi={chi}, expected {1 - 2 * mesh.genus}"
    assert len({tuple(sorted(f)) for f in faces.tolist()}) == F, "duplicate faces"
    assert all(len(set(f)) == 3 for f in faces.tolist()), "degenerate face"
    cnt = np.bincount(mesh.face_edges.ravel(), minlength=E)
    assert cnt.max() <= 2 and cnt.min() >= 1, "non-manifold edge"
    assert (cnt == 1).sum() == len(mesh.boundary), "boundary edge count mismatch"
    assert np.array_equal(cnt == 1, mesh.bnd_edge_mask), "boundary edges mismatch"
    directed = [(f[k], f[(k + 1) % 3]) for f in faces.tolist() for k in range(3)]
    assert len(set(directed)) == len(directed), "orientation not coherent"
    # vertex links: a cycle (interior) or a path (boundary)
    for v in range(V):
        link = [(f[(k + 1) % 3], f[(k + 2) % 3]) for f in faces.tolist()
                for k in range(3) if f[k] == v]
        deg = defaultdict(int)
        for a, b in link:
            deg[a] += 1
            deg[b] += 1
        ends = sum(1 for d in deg.values() if d == 1)
        assert all(d <= 2 for d in deg.values()), f"bad link at {v}"
        assert ends == (2 if v in bset else 0), f"bad link at {v}"
        # connectedness of link
        adj = defaultdict(list)
        for a, b in link:
            adj[a].append(b)
            adj[b].append(a)
        seen, stack = set(), [next(iter(adj))]
        while stack:
            x = stack.pop()
            if x not in seen:
                seen.add(x)
                stack.extend(adj[x])
        assert len(seen) == len(adj), f"disconnected link at {v}"
    bfaces = np.bincount(faces.ravel(), minlength=V)[mesh.boundary]
    bval = np.bincount(edges.ravel(), minlength=V)[mesh.boundary]
    mesh.info = {"V": V, "E": E, "F": F, "chi": chi, "n_boundary": len(mesh.boundary),
                 "min_boundary_faces": int(bfaces.min()),
                 "min_boundary_valence": int(bval.min())}


# ---------------------------------------------------------------------------
# Metric quantities
# ---------------------------------------------------------------------------


def triangle_barrier(slack: np.ndarray, delta: float = 1e-3) -> float:
    """Log barrier ``-BARRIER * log(slack)``, extended past ``slack = delta``.

    Below ``delta`` the barrier continues linearly (C^1) and a stiff quadratic
    penalty is added, so the objective stays finite and continuous, which
    Powell's line searches need; the polish step restores strict validity.
    """
    inner = np.maximum(slack, delta)
    out = np.maximum(delta - slack, 0.0)
    val = -np.log(inner) + out / delta
    return float(BARRIER * val.sum() + PENALTY * (out @ out))


def heron_area_grad(lengths: np.ndarray, face_edges: np.ndarray):
    """Total Heron area and its gradient with respect to all edge lengths."""
    a, b, c = (lengths[face_edges[:, k]] for k in range(3))
    q = 2 * (a * a * b * b + b * b * c * c + c * c * a * a) - a**4 - b**4 - c**4
    q = np.maximum(q, 1e-14)
    s = np.sqrt(q)
    area = 0.25 * s
    grad = np.zeros_like(lengths)
    # dA/da = a (b^2 + c^2 - a^2) / (2 sqrt(Q))
    for k, (x, y, z) in enumerate(((a, b, c), (b, c, a), (c, a, b))):
        np.add.at(grad, face_edges[:, k], x * (y * y + z * z - x * x) / (2 * s))
    return float(area.sum()), grad


def boundary_targets(n_b: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    ii, jj = np.triu_indices(n_b, k=1)
    theta = TWO_PI * np.arange(n_b) / n_b
    target = np.array([circle_geodesic_dist(theta[i], theta[j]) for i, j in zip(ii, jj)])
    return ii, jj, target


class PathDistance:
    """Boundary-to-boundary shortest paths on a (possibly Steiner-refined) graph.

    ``k = 0`` gives the plain edge graph of the triangulation. For ``k > 0``,
    each mesh edge carries k interior points, and inside every face (unfolded
    in the plane from its three edge lengths) all boundary nodes of that face
    are joined by straight segments. The Steiner graph distance is an upper
    bound on the true intrinsic geodesic distance and converges to it as k
    grows.
    """

    def __init__(self, mesh: Mesh, k: int = 0):
        self.mesh, self.k = mesh, k
        V, E = mesh.n_vertices, len(mesh.edges)
        self.n_nodes = V + E * k
        ts = np.arange(1, k + 1) / (k + 1)
        rows, cols, faces_of, dws = [], [], [], []
        seen: set[tuple[int, int]] = set()
        for fi, (A, B, C) in enumerate(mesh.faces.tolist()):
            verts = (A, B, C)
            nodes, weights = [], []  # barycentric coordinates wrt (A, B, C)
            for slot, vtx in enumerate(verts):
                bw = [0.0, 0.0, 0.0]
                bw[slot] = 1.0
                nodes.append(vtx)
                weights.append(bw)
            for slot, (p, q) in enumerate(((1, 2), (2, 0), (0, 1))):  # opp. A, B, C
                ek = mesh.face_edges[fi, slot]
                u = mesh.edges[ek][0]
                pu, pv = (p, q) if verts[p] == u else (q, p)
                for t_i, t in enumerate(ts):
                    bw = [0.0, 0.0, 0.0]
                    bw[pu], bw[pv] = 1.0 - t, t  # parameter measured from vertex u
                    nodes.append(V + ek * k + t_i)
                    weights.append(bw)
            for x in range(len(nodes)):
                for y in range(x + 1, len(nodes)):
                    key = (min(nodes[x], nodes[y]), max(nodes[x], nodes[y]))
                    if key in seen:  # same segment along a shared edge
                        continue
                    seen.add(key)
                    rows.append(key[0])
                    cols.append(key[1])
                    faces_of.append(fi)
                    dws.append(np.array(weights[x]) - np.array(weights[y]))
        self.rows = np.array(rows + cols)
        self.cols = np.array(cols + rows)
        self.faces_of = np.array(faces_of)
        self.dw = np.array(dws)
        self.ii, self.jj, self.target = boundary_targets(len(mesh.boundary))
        self.bnd = np.array(mesh.boundary)
        # cache the CSR pattern: ``order`` maps CSR slots to segment weights, so a
        # call only refills ``data`` (both directions are stored explicitly)
        n, m = self.n_nodes, len(rows)
        pat = csr_matrix((np.arange(1, 2 * m + 1, dtype=float), (self.rows, self.cols)),
                         shape=(n, n))
        pat.sort_indices()
        self.order = (pat.data.astype(np.int64) - 1) % m
        self.graph = pat

    def __call__(self, lengths: np.ndarray) -> np.ndarray:
        """Distances d(b_i, b_j) for all boundary pairs i < j."""
        fe = self.mesh.face_edges
        lengths = np.maximum(lengths, 1e-9)
        la, lb, lc = (lengths[fe[:, s]] for s in range(3))  # |BC|, |CA|, |AB|
        # planar layout of each face: A = (0, 0), B = (lc, 0), C = (x, y)
        x = (lb * lb + lc * lc - la * la) / (2 * lc)
        y = np.sqrt(np.maximum(lb * lb - x * x, 0.0))
        f = self.faces_of
        d1, d2 = self.dw[:, 1], self.dw[:, 2]
        w = np.maximum(np.hypot(d1 * lc[f] + d2 * x[f], d2 * y[f]), 1e-12)
        g = self.graph.copy()
        g.data = w[self.order]
        dist = shortest_path(g, method="D", directed=True, indices=self.bnd)
        return dist[self.ii, self.bnd[self.jj]]


# ---------------------------------------------------------------------------
# Optimization
# ---------------------------------------------------------------------------


def corner_angles(lengths: np.ndarray, faces: np.ndarray, face_edges: np.ndarray,
                  n_vertices: int) -> np.ndarray:
    """Total cone angle at every vertex: sum of incident face corner angles."""
    la, lb, lc = (lengths[face_edges[:, s]] for s in range(3))  # opposite A, B, C
    tot = np.zeros(n_vertices)
    for k, (x, y, z) in enumerate(((la, lb, lc), (lb, lc, la), (lc, la, lb))):
        cos = (y * y + z * z - x * x) / np.maximum(2 * y * z, 1e-15)
        np.add.at(tot, faces[:, k], np.arccos(np.clip(cos, -1.0, 1.0)))
    return tot


class FillingProblem:
    def __init__(self, mesh: Mesh, steiner_k: int = 5, certify_k: int = 16):
        self.mesh = mesh
        n_b = len(mesh.boundary)
        self.fixed = mesh.bnd_edge_mask
        self.free = ~self.fixed
        self.base = np.full(len(mesh.edges), TWO_PI / n_b)
        self.steiner_k, self.certify_k = steiner_k, certify_k
        self.pd0 = PathDistance(mesh, 0)  # plain edge graph (cheap pre-filter)
        self.pd = PathDistance(mesh, steiner_k)  # optimization graph
        self.cert = PathDistance(mesh, certify_k)  # certification graph
        self.bnd = np.array(mesh.boundary)
        # strict triangle inequalities: rows (+1, +1, -1) over each face's edges
        fe = mesh.face_edges
        T = np.zeros((3 * len(fe), len(mesh.edges)))
        for fi, (a, b, c) in enumerate(fe):
            for r, (p, q, s) in enumerate(((a, b, c), (b, c, a), (c, a, b))):
                T[3 * fi + r, [p, q]] += 1.0
                T[3 * fi + r, s] -= 1.0
        self.T_full = T
        self.T = T[:, self.free]
        self.T_const = T[:, self.fixed] @ self.base[self.fixed] - EPS_TRI
        self.nfev = 0

    def lengths(self, x: np.ndarray) -> np.ndarray:
        ell = self.base.copy()
        ell[self.free] = x
        return ell

    def boundary_angles(self, x: np.ndarray) -> np.ndarray:
        m = self.mesh
        tot = corner_angles(self.lengths(x), m.faces, m.face_edges, m.n_vertices)
        return tot[self.bnd]

    def metrics(self, x) -> dict:
        ell = self.lengths(x)
        A, _ = heron_area_grad(ell, self.mesh.face_edges)
        fe = self.mesh.face_edges
        la, lb, lc = (ell[fe[:, s]] for s in range(3))
        # face "fatness" 2 r / R: 1 for equilateral, 0 for needles
        s = (la + lb + lc) / 2
        areas = np.sqrt(np.maximum(s * (s - la) * (s - lb) * (s - lc), 0))
        fat = 2 * (areas / s) / (la * lb * lc / np.maximum(4 * areas, 1e-15))
        tgt = self.pd.target
        return {
            "area": A,
            "area_over_2pi": A / TWO_PI,
            "min_triangle_slack": float((self.T_full @ ell).min()),
            "median_face_fatness": float(np.median(fat)),
            "min_boundary_angle_over_pi": float(self.boundary_angles(x).min() / np.pi),
            "max_violation_edge_graph": float(max(0.0, (tgt - self.pd0(ell)).max())),
            f"k{self.steiner_k}_violation": float(max(0.0, (tgt - self.pd(ell)).max())),
        }

    # -- feasibility -----------------------------------------------------------

    def tri_slack(self, x: np.ndarray) -> float:
        """Minimum of ``l_a + l_b - l_c`` over all faces and corners."""
        return float((self.T @ x + self.T_const).min() + EPS_TRI)

    @staticmethod
    def _viol(pd: PathDistance, ell: np.ndarray) -> float:
        return float(max(0.0, (pd.target - pd(ell)).max()))

    def k16_violation(self, x: np.ndarray) -> float:
        return self._viol(self.cert, self.lengths(x))

    def ok(self, x: np.ndarray, tol: float) -> bool:
        """Strict feasibility test, cheapest checks first.

        Every Steiner graph gives an *upper* bound on intrinsic distance, so a
        violation on the edge graph or the k = 5 graph is already a real one and
        rejects ``x`` without building the expensive k = 16 distances.
        """
        if self.tri_slack(x) < EPS_TRI - 1e-9:
            return False
        if self.boundary_angles(x).min() < np.pi:
            return False
        ell = self.lengths(x)
        if self._viol(self.pd0, ell) > tol or self._viol(self.pd, ell) > tol:
            return False
        return self._viol(self.cert, ell) <= tol

    def corner_cut(self, x: np.ndarray) -> float:
        """Exact lower bound on the true violation from boundary corner cuts.

        Unfold the fan of faces around each boundary vertex ``v`` into the plane.
        If its total angle is below ``pi`` and the straight chord between the two
        boundary neighbours of ``v`` crosses every interior spoke within its
        length, that chord is a genuine path in the surface, so
        ``d_S1(u_0, u_m) - |chord|`` is a lower bound on the violation.
        """
        mesh = self.mesh
        ell = self.lengths(x)
        eid = {tuple(e): i for i, e in enumerate(mesh.edges.tolist())}

        def length(u, v):
            return ell[eid[(min(u, v), max(u, v))]]

        n_b = len(mesh.boundary)
        target = 2.0 * TWO_PI / n_b if n_b > 2 else 0.0
        best = 0.0
        for v in mesh.boundary:
            nxt = {}
            for f in mesh.faces.tolist():
                if v in f:
                    k = f.index(v)
                    nxt[f[(k + 1) % 3]] = f[(k + 2) % 3]
            u = next(a for a in nxt if a not in nxt.values())  # start of the link path
            chain = [u]
            while chain[-1] in nxt:
                chain.append(nxt[chain[-1]])
            theta = [0.0]
            for a, b in zip(chain, chain[1:]):
                la, lb, lab = length(v, a), length(v, b), length(a, b)
                cos = (la * la + lb * lb - lab * lab) / (2 * la * lb)
                theta.append(theta[-1] + float(np.arccos(np.clip(cos, -1.0, 1.0))))
            total = theta[-1]
            if total >= np.pi:
                continue
            p0 = length(v, chain[0]) * np.array([1.0, 0.0])
            p1 = length(v, chain[-1]) * np.array([np.cos(total), np.sin(total)])
            ok = True
            for w, th in zip(chain[1:-1], theta[1:-1]):
                d = np.array([np.cos(th), np.sin(th)])  # ray from v
                m = np.array([d, p0 - p1]).T
                r = np.linalg.solve(m, p0)[0]  # ray parameter at the chord
                ok &= bool(0.0 < r <= length(v, w))
            if ok:
                best = max(best, target - float(np.linalg.norm(p1 - p0)))
        return max(0.0, best)

    def certify(self, x: np.ndarray, strict_tol: float) -> dict:
        out = self.metrics(x)
        out["k16_violation"] = self.k16_violation(x)
        out["exact_lower_bound"] = self.corner_cut(x)
        out["certified"] = bool(out["exact_lower_bound"] == 0.0
                                and out["k16_violation"] <= CERT_TOL
                                and out["min_triangle_slack"] >= EPS_TRI - 1e-9
                                and out["min_boundary_angle_over_pi"] >= 1.0)
        out["strictly_feasible"] = bool(out["certified"]
                                        and out["k16_violation"] <= strict_tol)
        return out

    # -- feasible initialization ------------------------------------------------

    def hemisphere_profile(self, rng: np.random.Generator | None = None,
                           jitter: float = 0.0) -> np.ndarray:
        """Edge lengths ``ell_init`` from a hemisphere-like polar profile.

        Each vertex gets a polar angle ``phi`` that decreases with its
        combinatorial depth (hop distance from the boundary): boundary vertices
        sit on the equator ``phi = pi/2`` and the deepest vertices near the pole.
        An edge ``uv`` gets the length of a small step on the unit sphere,
        ``sqrt(dphi^2 + (h sin phi_mid)^2)`` with ``h = 2 pi / n_b``, so boundary
        edges reproduce ``2 pi / n_b`` exactly and the two spokes of every
        boundary face are equal (which keeps those faces valid under scaling).

        With ``rng``, restarts draw a random depth exponent ``gamma`` and jitter
        the polar angle of every *interior* vertex multiplicatively; boundary
        vertices stay on the equator, so boundary faces stay isosceles.
        """
        mesh = self.mesh
        n_b = len(mesh.boundary)
        adj = defaultdict(list)
        for u, v in mesh.edges.tolist():
            adj[u].append(v)
            adj[v].append(u)
        depth = np.full(mesh.n_vertices, -1)
        queue = deque(mesh.boundary)
        depth[mesh.boundary] = 0
        while queue:
            u = queue.popleft()
            for v in adj[u]:
                if depth[v] < 0:
                    depth[v] = depth[u] + 1
                    queue.append(v)
        gamma = 1.0 if rng is None else float(rng.uniform(0.6, 1.6))
        t = (depth / (depth.max() + 1.0)) ** gamma
        phi = 0.5 * np.pi * (1.0 - t)
        if rng is not None and jitter > 0:
            inner = depth > 0
            phi[inner] *= np.exp(jitter * rng.standard_normal(inner.sum()))
            phi[inner] = np.clip(phi[inner], 0.02, 0.5 * np.pi - 0.02)
        pu, pv = phi[mesh.edges[:, 0]], phi[mesh.edges[:, 1]]
        h = TWO_PI / n_b
        return np.hypot(pu - pv, h * np.sin(0.5 * (pu + pv)))

    def feasible_start(self, tol: float, rng=None, jitter: float = 0.0,
                       growth: float = 1.15, max_steps: int = 80):
        """Scale ``c * ell_init`` up until every strict constraint holds.

        For large ``c`` every path that leaves the boundary cycle is long, so the
        shortest boundary-to-boundary paths run along the boundary edges, whose
        lengths reproduce the circle arcs, and with four faces per boundary
        vertex every boundary cone angle exceeds ``pi``. A final bisection on
        ``c`` returns the smallest feasible scale found.
        """
        prof = self.hemisphere_profile(rng, jitter)[self.free]
        lo, c = None, 0.5
        for _ in range(max_steps):
            if self.ok(c * prof, tol):
                break
            lo, c = c, c * growth
        else:
            raise RuntimeError("no feasible scale found for the hemisphere profile")
        if lo is not None:
            hi = c
            for _ in range(20):
                mid = 0.5 * (lo + hi)
                lo, hi = (lo, mid) if self.ok(mid * prof, tol) else (mid, hi)
            c = hi
        return c * prof, c

    # -- penalized objective ---------------------------------------------------

    def objective(self, x: np.ndarray) -> float:
        """Heron area + Steiner hinge (k = 5) + boundary-angle hinge + log barrier."""
        self.nfev += 1
        ell = self.lengths(x)
        area = heron_area_grad(ell, self.mesh.face_edges)[0]
        hinge = np.maximum(0.0, self.pd.target - self.pd(ell))
        ang = np.maximum(0.0, np.pi + ANGLE_MARGIN - self.boundary_angles(x))
        return (area + PENALTY * float(hinge @ hinge) + ANGLE_PENALTY * float(ang @ ang)
                + triangle_barrier(self.T @ x + self.T_const))

    def run_powell(self, x0: np.ndarray, maxiter: int, maxfev: int):
        self.nfev = 0
        t0 = time.time()
        res = minimize(self.objective, x0, method="Powell",
                       bounds=[(EPS_LEN, None)] * len(x0),
                       options={"maxiter": maxiter, "maxfev": maxfev,
                                "xtol": 1e-6, "ftol": 1e-10})
        f0, f1 = self.objective(x0), self.objective(res.x)
        x = res.x if f1 <= f0 else x0
        info = {"method": "Powell", "maxiter": maxiter, "maxfev": maxfev,
                "message": str(res.message), "nit": int(res.nit), "nfev": int(res.nfev),
                "objective": float(min(f0, f1)), "seconds": round(time.time() - t0, 2)}
        info.update(self.metrics(x))
        return x, info

    def run_nelder_mead(self, x0: np.ndarray, maxiter: int, maxfev: int,
                        step: float = 0.01):
        """Adaptive Nelder-Mead polish from a simplex of 1% coordinate steps."""
        self.nfev = 0
        t0 = time.time()
        n = len(x0)
        simplex = np.vstack([x0, x0 + np.diag(step * np.maximum(x0, 10 * EPS_LEN))])
        res = minimize(self.objective, x0, method="Nelder-Mead",
                       bounds=[(EPS_LEN, None)] * n,
                       options={"maxiter": maxiter, "maxfev": maxfev, "adaptive": True,
                                "initial_simplex": simplex,
                                "xatol": 1e-7, "fatol": 1e-10})
        f0, f1 = self.objective(x0), self.objective(res.x)
        x = res.x if f1 <= f0 else x0
        info = {"method": "Nelder-Mead", "adaptive": True, "maxiter": maxiter,
                "maxfev": maxfev, "message": str(res.message), "nit": int(res.nit),
                "nfev": int(res.nfev), "objective": float(min(f0, f1)),
                "seconds": round(time.time() - t0, 2)}
        info.update(self.metrics(x))
        return x, info

    # -- feasibility restoration -----------------------------------------------

    def restore(self, x: np.ndarray, x_safe: np.ndarray, tol: float, iters: int = 40):
        """Return the cheapest strictly feasible point on two 1-D families.

        (a) radial rescaling ``s * x`` of the interior lengths, with ``s`` found by
        bracketing and bisection, and (b) the segment from ``x`` to the strictly
        feasible start ``x_safe`` (triangle inequalities are linear, so the
        segment stays valid). Both bisections keep ``hi`` feasible, so whatever is
        returned satisfies ``ok(., tol)``; the lower-area candidate wins.
        """
        def bisect(path, lo, hi):  # path(lo) infeasible, path(hi) feasible
            for _ in range(iters):
                mid = 0.5 * (lo + hi)
                lo, hi = (lo, mid) if self.ok(path(mid), tol) else (mid, hi)
            return hi

        cands = []

        def scale(s):
            return s * x

        if self.ok(x, tol):
            lo = 0.5
            while lo < 1.0 and self.ok(scale(lo), tol):
                lo = 0.5 * (1.0 + lo) if lo > 0.9 else lo * 0.5 + 0.25
                if lo < 1e-3:
                    break
            s = 1.0 if lo >= 1.0 else bisect(scale, lo, 1.0)
            cands.append((scale(s), {"mode": "scale", "scale": s}))
        else:
            s, step = 1.0, 0.01
            while s < 8.0:
                s_next = s + step
                if self.tri_slack(scale(s_next)) < EPS_TRI - 1e-9:
                    break
                if self.ok(scale(s_next), tol):
                    s = bisect(scale, s, s_next)
                    cands.append((scale(s), {"mode": "scale", "scale": s}))
                    break
                s, step = s_next, 2 * step

        def blend(t):
            return (1.0 - t) * x + t * x_safe

        if not self.ok(x, tol):
            t = bisect(blend, 0.0, 1.0)
            cands.append((blend(t), {"mode": "blend_to_start", "t": t}))
        best = min(cands, key=lambda c: heron_area_grad(self.lengths(c[0]),
                                                        self.mesh.face_edges)[0])
        return best


# ---------------------------------------------------------------------------
# Flat baseline
# ---------------------------------------------------------------------------


def flat_baseline(mesh: Mesh, prob: FillingProblem) -> dict:
    """Tutte-embed the genus-0 mesh in the plane, boundary on a circle of length 2*pi.

    The resulting flat disk has area ~ pi, but its straight chords are much
    shorter than the boundary arcs, so it violates the isometric constraint.
    """
    assert mesh.genus == 0
    n, n_b = mesh.n_vertices, len(mesh.boundary)
    R = (TWO_PI / n_b) / (2 * np.sin(np.pi / n_b))  # regular n_b-gon, perimeter 2*pi
    pos = np.zeros((n, 2))
    theta = TWO_PI * np.arange(n_b) / n_b
    for b, t in zip(mesh.boundary, theta):
        pos[b] = R * np.cos(t), R * np.sin(t)
    bset = set(mesh.boundary)
    interior = [v for v in range(n) if v not in bset]
    idx = {v: i for i, v in enumerate(interior)}
    L = np.zeros((len(interior), len(interior)))
    rhs = np.zeros((len(interior), 2))
    for u, v in mesh.edges:
        for p, q in ((u, v), (v, u)):
            if p in idx:
                L[idx[p], idx[p]] += 1
                if q in idx:
                    L[idx[p], idx[q]] -= 1
                else:
                    rhs[idx[p]] += pos[q]
    pos[interior] = np.linalg.solve(L, rhs)
    ell = np.linalg.norm(pos[mesh.edges[:, 0]] - pos[mesh.edges[:, 1]], axis=1)
    m = prob.metrics(ell[prob.free])
    m["k16_violation"] = prob.k16_violation(ell[prob.free])
    m["description"] = "Tutte embedding in R^2, boundary = regular n_b-gon of perimeter 2*pi"
    m["antipodal_chord"] = 2 * R
    return m


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------


def run_restart(genus: int, restart: int, cfg: dict) -> dict:
    """One restart for one genus: feasible start -> Powell -> Nelder-Mead -> restore."""
    t_all = time.time()
    mesh = build_mesh(genus, n_b=cfg["n_boundary"])
    prob = FillingProblem(mesh, steiner_k=cfg["steiner_k"], certify_k=cfg["certify_k"])
    tol = cfg["strict_tol"]
    rng = None if restart == 0 else np.random.default_rng(1000 * genus + restart)
    tag = f"g={genus} r={restart}"

    t0 = time.time()
    x0, c0 = prob.feasible_start(tol, rng, jitter=cfg["jitter"])
    start = {"hemisphere_scale_c": c0, "seconds": round(time.time() - t0, 2)}
    start.update(prob.certify(x0, tol))
    print(f"  [{tag} start ] c={c0:.3f} A={start['area']:.4f} "
          f"k16={start['k16_violation']:.1e} ang={start['min_boundary_angle_over_pi']:.3f}pi "
          f"({start['seconds']} s)", flush=True)

    x1, pw = prob.run_powell(x0, cfg["maxiter"], cfg["maxfev"])
    kk = f"k{prob.steiner_k}_violation"
    print(f"  [{tag} powell] A={pw['area']:.4f} k{prob.steiner_k}={pw[kk]:.1e} "
          f"nit={pw['nit']} nfev={pw['nfev']} ({pw['seconds']} s)", flush=True)
    x2, nm = prob.run_nelder_mead(x1, cfg["nm_maxiter"], cfg["nm_maxfev"])
    print(f"  [{tag} nm    ] A={nm['area']:.4f} k{prob.steiner_k}={nm[kk]:.1e} "
          f"nfev={nm['nfev']} ({nm['seconds']} s)", flush=True)

    t0 = time.time()
    x3, how = prob.restore(x2, x0, tol)
    final = {**how, "seconds": round(time.time() - t0, 2)}
    final.update(prob.certify(x3, tol))
    print(f"  [{tag} final ] {how} A={final['area']:.4f} A/2pi={final['area_over_2pi']:.4f} "
          f"k16={final['k16_violation']:.1e} lb={final['exact_lower_bound']:.1e} "
          f"certified={final['certified']} strict={final['strictly_feasible']}", flush=True)
    return {"genus": genus, "restart": restart, "seed": None if rng is None
            else 1000 * genus + restart, "mesh": mesh.info,
            "free_edges": int(prob.free.sum()), "feasible_start": start, "powell": pw,
            "nelder_mead": nm, "final": final,
            "final_edge_lengths": prob.lengths(x3).tolist(),
            "seconds": round(time.time() - t_all, 2)}


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--maxiter", type=int, default=2000, help="Powell maxiter")
    ap.add_argument("--maxfev", type=int, default=60000,
                    help="Powell objective-evaluation budget per restart")
    ap.add_argument("--nm-maxiter", type=int, default=20000)
    ap.add_argument("--nm-maxfev", type=int, default=20000,
                    help="Nelder-Mead objective-evaluation budget per restart")
    ap.add_argument("--restarts", type=int, default=4)
    ap.add_argument("--jitter", type=float, default=0.25,
                    help="log-normal jitter of interior polar angles for restarts > 0")
    ap.add_argument("--strict-tol", type=float, default=1e-12,
                    help="k = 16 violation treated as zero (floating-point roundoff)")
    ap.add_argument("--n-boundary", type=int, default=16)
    ap.add_argument("--steiner-k", type=int, default=5)
    ap.add_argument("--certify-k", type=int, default=16)
    ap.add_argument("--genera", type=int, nargs="+", default=[0, 1, 2])
    ap.add_argument("--workers", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--out", default="benchmarks/genus_search.json")
    args = ap.parse_args()
    cfg = vars(args)

    t0 = time.time()
    # largest genus first: its restarts are the slowest, so they start earliest
    jobs = [(g, r) for g in sorted(args.genera, reverse=True) for r in range(args.restarts)]
    print(f"{len(jobs)} jobs on {args.workers} workers", flush=True)
    runs = []
    with ProcessPoolExecutor(max_workers=args.workers) as ex:
        futs = {ex.submit(run_restart, g, r, cfg): (g, r) for g, r in jobs}
        for fut in as_completed(futs):
            runs.append(fut.result())
    runs.sort(key=lambda r: (r["genus"], r["restart"]))

    best = {}
    for g in args.genera:
        ok = [r for r in runs if r["genus"] == g and r["final"]["strictly_feasible"]]
        if ok:
            b = min(ok, key=lambda r: r["final"]["area"])
            f = b["final"]
            best[str(g)] = {"restart": b["restart"], "area": f["area"],
                            "area_over_2pi": f["area_over_2pi"],
                            "k16_violation": f["k16_violation"],
                            "exact_lower_bound": f["exact_lower_bound"],
                            "min_boundary_angle_over_pi": f["min_boundary_angle_over_pi"],
                            "median_face_fatness": f["median_face_fatness"]}
            print(f"genus {g}: best strictly feasible A={f['area']:.4f} "
                  f"A/2pi={f['area_over_2pi']:.4f} (restart {b['restart']})")
        else:
            best[str(g)] = None
            print(f"genus {g}: no strictly feasible restart")

    flat = None
    if 0 in args.genera:
        mesh = build_mesh(0, n_b=args.n_boundary)
        flat = flat_baseline(mesh, FillingProblem(mesh, args.steiner_k, args.certify_k))
    out = {
        "description": "Discrete piecewise-flat fillings of S^1 (length 2*pi): minimize "
                       "Heron area over intrinsic edge lengths subject to strict triangle "
                       "inequalities, boundary cone angles >= pi, and d(b_i, b_j) >= "
                       "d_S1(b_i, b_j). Two-ring boundary collar (4 faces per boundary "
                       "vertex); multi-restart Powell -> adaptive Nelder-Mead on a "
                       "penalized objective (k = 5 Steiner graph); feasibility restoration "
                       "and certification on a k = 16 Steiner graph plus the exact "
                       "corner-cut lower bound.",
        "config": {**cfg, "eps_triangle": EPS_TRI, "eps_length": EPS_LEN,
                   "penalty": PENALTY, "angle_penalty": ANGLE_PENALTY,
                   "angle_margin": ANGLE_MARGIN, "barrier": BARRIER,
                   "certified_tol": CERT_TOL},
        "reference": {"pi": np.pi, "two_pi": TWO_PI},
        "best_strictly_feasible": best,
        "flat_baseline_genus0": flat,
        "runs": runs,
        "total_seconds": round(time.time() - t0, 2),
    }
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).write_text(json.dumps(out, indent=2) + "\n")
    print(f"\nSaved {args.out} ({out['total_seconds']} s)")


if __name__ == "__main__":
    main()

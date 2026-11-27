"""Numerical exploration of discrete fillings of S^1 (length 2*pi), genus 0-2.

Each filling is an orientable simplicial surface of genus g (Euler
characteristic chi = 1 - 2g) with one boundary cycle of n_b vertices. Its
metric is given by *intrinsic edge lengths* (a piecewise-flat Riemannian
metric), not by coordinates in R^2 or R^3, so a triangle's area comes from
Heron's formula.

The boundary edges are fixed at length 2*pi / n_b, so the boundary cycle has
length exactly 2*pi. The interior edge lengths are optimized to

    minimize   sum_faces Heron(l_a, l_b, l_c)
    subject to l_a + l_b - l_c >= eps                  (strict triangle ineq.)
               d(b_i, b_j) >= d_{S^1}(b_i, b_j)         (isometric boundary)

d is computed with scipy.sparse.csgraph.shortest_path on a Steiner graph
(k points per edge, straight segments inside each face unfolded in the
plane), which converges to the true intrinsic distance as k grows.

Solver (deterministic, ~30 s for g = 0, 1, 2):

1. Feasible start. Edge lengths ``ell_init`` come from a hemisphere-like
   polar profile (polar angle decreasing with combinatorial depth); the
   interior lengths ``c * ell_init`` are scaled up until the k = 3 and k = 8
   Steiner violations vanish (to roundoff) with strict triangle inequalities.
2. Powell (``maxiter=400``, capped by ``maxfev``) minimizes
   Heron area + 1e4 * sum max(0, d_S1 - d_int)^2 (k = 3) + extended log
   barrier on the triangle slacks. Powell needs no gradients.
3. Polish. The interior lengths are rescaled radially (or, if that would
   break a triangle inequality, blended back toward the start) by bisection
   until the k = 8 violation is <= 1e-4.

Every result is certified with the k = 8 Steiner graph and audited with a
finer k = 16 graph and with an exact corner-cut lower bound. Both Steiner
graphs give *upper* bounds on distance, so a violation they report is real,
but a zero reading is not a proof of feasibility. On this collar mesh,
boundary vertices lying in only two faces have total angle < pi, so a chord
cuts the corner and the true violation is positive (~0.02) even when the
k = 8 reading is <= 1e-4.

Usage:  .venv/bin/python3 scripts/explore_genus2.py
"""

from __future__ import annotations

import argparse
import json
import time
from collections import defaultdict, deque
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


def build_mesh(genus: int, n_b: int = 8, levels: int = 1) -> Mesh:
    surf = closed_surface(genus)
    surf = surf[1:]  # punch one hole -> one boundary 3-cycle
    for _ in range(levels):
        surf = subdivide(surf)
    surf, bnd = add_collar(surf, n_b)

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
    mesh.info = {"V": V, "E": E, "F": F, "chi": chi, "n_boundary": len(mesh.boundary)}


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
        n = self.n_nodes
        g = csr_matrix((np.concatenate([w, w]), (self.rows, self.cols)), shape=(n, n))
        dist = shortest_path(g, method="D", directed=False, indices=self.bnd)
        return dist[self.ii, self.bnd[self.jj]]


# ---------------------------------------------------------------------------
# Optimization
# ---------------------------------------------------------------------------


class FillingProblem:
    def __init__(self, mesh: Mesh, steiner_k: int = 3, certify_k: int = 8,
                 audit_k: int = 16):
        self.mesh = mesh
        n_b = len(mesh.boundary)
        self.fixed = mesh.bnd_edge_mask
        self.free = ~self.fixed
        self.base = np.full(len(mesh.edges), TWO_PI / n_b)
        self.steiner_k, self.certify_k = steiner_k, certify_k
        self.pd = {0: PathDistance(mesh, 0), steiner_k: PathDistance(mesh, steiner_k)}
        self.cert = PathDistance(mesh, certify_k)
        self.audit_k = audit_k
        self.audit_pd = PathDistance(mesh, audit_k)
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

    def area(self, x) -> float:
        return heron_area_grad(self.lengths(x), self.mesh.face_edges)[0]

    def metrics(self, x) -> dict:
        ell = self.lengths(x)
        A, _ = heron_area_grad(ell, self.mesh.face_edges)
        fe = self.mesh.face_edges
        la, lb, lc = (ell[fe[:, s]] for s in range(3))
        # face "fatness" 2 r / R: 1 for equilateral, 0 for needles
        s = (la + lb + lc) / 2
        areas = np.sqrt(np.maximum(s * (s - la) * (s - lb) * (s - lc), 0))
        fat = 2 * (areas / s) / (la * lb * lc / np.maximum(4 * areas, 1e-15))
        tgt = self.pd[0].target
        return {
            "area": A,
            "area_over_2pi": A / TWO_PI,
            "min_triangle_slack": float((self.T_full @ ell).min()),
            "median_face_fatness": float(np.median(fat)),
            "max_violation_edge_graph": float(max(0.0, (tgt - self.pd[0](ell)).max())),
            f"max_violation_steiner_k{self.steiner_k}": float(
                max(0.0, (tgt - self.pd[self.steiner_k](ell)).max())),
            f"max_violation_intrinsic_k{self.certify_k}": float(
                max(0.0, (tgt - self.cert(ell)).max())),
        }

    # -- feasible initialization ------------------------------------------------

    def hemisphere_profile(self) -> np.ndarray:
        """Edge lengths ``ell_init`` from a hemisphere-like polar profile.

        Each vertex gets a polar angle ``phi`` that decreases linearly with its
        combinatorial depth (hop distance from the boundary): boundary vertices
        sit on the equator ``phi = pi/2`` and the deepest vertices near the pole.
        An edge ``uv`` gets the length of a small step on the unit sphere,
        ``sqrt(dphi^2 + (h sin phi_mid)^2)`` with ``h = 2 pi / n_b``, so boundary
        edges reproduce ``2 pi / n_b`` exactly and the two spokes of every
        boundary face are equal (which keeps those faces valid under scaling).
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
        phi = 0.5 * np.pi * (1.0 - depth / (depth.max() + 1.0))
        pu, pv = phi[mesh.edges[:, 0]], phi[mesh.edges[:, 1]]
        h = TWO_PI / n_b
        return np.hypot(pu - pv, h * np.sin(0.5 * (pu + pv)))

    def tri_slack(self, x: np.ndarray) -> float:
        """Minimum of ``l_a + l_b - l_c`` over all faces and corners."""
        return float((self.T @ x + self.T_const).min() + EPS_TRI)

    def violation(self, x: np.ndarray, k: int | None = None) -> float:
        """Max boundary-isometry violation ``max(0, d_S1 - d_int)`` on graph k."""
        pd = self.cert if k is None else self.pd[k]
        return float(max(0.0, (pd.target - pd(self.lengths(x))).max()))

    def audit(self, x: np.ndarray) -> dict:
        """Violation on a finer Steiner graph (k = audit_k): an independent check."""
        pd = self.audit_pd
        v = float(max(0.0, (pd.target - pd(self.lengths(x))).max()))
        return {f"max_violation_audit_k{self.audit_k}": v}

    def corner_cut(self, x: np.ndarray) -> dict:
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
        best, min_angle = 0.0, np.inf
        for pos, v in enumerate(mesh.boundary):
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
            min_angle = min(min_angle, total)
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
        return {"violation_lower_bound_corner_cut": max(0.0, best),
                "min_boundary_angle_over_pi": float(min_angle / np.pi)}

    def ok(self, x: np.ndarray, tol: float) -> bool:
        return (self.tri_slack(x) >= EPS_TRI - 1e-9 and self.violation(x) <= tol
                and self.violation(x, self.steiner_k) <= tol)

    def feasible_start(self, growth: float = 1.25, max_steps: int = 60):
        """Scale ``c * ell_init`` up until the boundary constraints hold exactly.

        For large ``c`` every path that leaves the boundary cycle is long, so the
        shortest boundary-to-boundary paths run along the boundary edges, whose
        lengths reproduce the circle arcs: the violation is zero (up to roundoff).
        """
        prof = self.hemisphere_profile()[self.free]
        c = 1.0
        for _ in range(max_steps):
            x = c * prof
            if self.ok(x, tol=1e-12):
                return x, c
            c *= growth
        raise RuntimeError("no feasible scale found for the hemisphere profile")

    # -- penalized objective ---------------------------------------------------

    def objective(self, x: np.ndarray) -> float:
        """Heron area + 1e4 * squared hinge on d_S1 - d_int + log barrier (triangles)."""
        self.nfev += 1
        ell = self.lengths(x)
        area = heron_area_grad(ell, self.mesh.face_edges)[0]
        pd = self.pd[self.steiner_k]
        hinge = np.maximum(0.0, pd.target - pd(ell))
        return (area + PENALTY * float(hinge @ hinge)
                + triangle_barrier(self.T @ x + self.T_const))

    def solve(self, x0: np.ndarray, maxiter: int = 400, maxfev: int = 4000):
        """Derivative-free Powell on the penalized objective, from a feasible x0."""
        self.nfev = 0
        t0 = time.time()
        res = minimize(self.objective, x0, method="Powell",
                       bounds=[(EPS_LEN, None)] * len(x0),
                       options={"maxiter": maxiter, "maxfev": maxfev,
                                "xtol": 1e-4, "ftol": 1e-7})
        x = res.x if self.objective(res.x) <= self.objective(x0) else x0
        info = {"method": "Powell", "maxiter": maxiter, "maxfev": maxfev,
                "message": str(res.message), "nit": int(res.nit), "nfev": int(res.nfev),
                "seconds": round(time.time() - t0, 2)}
        info.update(self.metrics(x))
        return x, info

    # -- certification polish --------------------------------------------------

    def polish(self, x: np.ndarray, x_safe: np.ndarray, tol: float = 1e-4,
               iters: int = 30):
        """Radially rescale the interior lengths until the k = 8 violation is <= tol.

        Searches the smallest interior scale ``s`` (bisection after bracketing
        upward from ``s = 1``, or downward when ``x`` is already feasible). If a
        scale would break a triangle inequality, it instead bisects along the
        segment from ``x`` to the feasible start ``x_safe`` (triangle
        inequalities are linear, so the segment stays valid).
        """
        def bisect(path, lo, hi):  # path(lo) infeasible, path(hi) feasible
            for _ in range(iters):
                mid = 0.5 * (lo + hi)
                lo, hi = (lo, mid) if self.ok(path(mid), tol) else (mid, hi)
            return hi

        def scale(s):
            return s * x

        if self.ok(x, tol):  # try shrinking toward smaller area
            lo = 0.5
            while lo < 1.0 and self.ok(scale(lo), tol):
                lo = 0.5 * (1.0 + lo)
            if lo >= 1.0:
                return x, {"mode": "scale", "scale": 1.0}
            s = bisect(scale, lo, 1.0)
            return scale(s), {"mode": "scale", "scale": s}
        s, step = 1.0, 0.01
        while s < 4.0:
            s_next = s + step
            if self.tri_slack(scale(s_next)) < EPS_TRI - 1e-9:
                break
            if self.ok(scale(s_next), tol):
                s = bisect(scale, s, s_next)
                return scale(s), {"mode": "scale", "scale": s}
            s, step = s_next, 2 * step

        def blend(t):
            return (1.0 - t) * x + t * x_safe

        t = bisect(blend, 0.0, 1.0)
        return blend(t), {"mode": "blend_to_start", "t": t}


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
    m["description"] = "Tutte embedding in R^2, boundary = regular n_b-gon of perimeter 2*pi"
    m["antipodal_chord"] = 2 * R
    return m


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------


def explore_genus(genus: int, args):
    mesh = build_mesh(genus, n_b=args.n_boundary)
    prob = FillingProblem(mesh, steiner_k=args.steiner_k, certify_k=args.certify_k,
                          audit_k=args.audit_k)
    ck = f"max_violation_intrinsic_k{prob.certify_k}"
    print(f"\n=== genus {genus}: {mesh.info} (free edges: {int(prob.free.sum())})", flush=True)

    t0 = time.time()
    x0, c0 = prob.feasible_start()
    start = {"hemisphere_scale_c": c0, "seconds": round(time.time() - t0, 2)}
    start.update(prob.metrics(x0))
    start.update(prob.audit(x0))
    start.update(prob.corner_cut(x0))
    print(f"  [start     ] c={c0:.3f} area={start['area']:.4f} "
          f"cert_viol={start[ck]:.1e} "
          f"corner_lb={start['violation_lower_bound_corner_cut']:.1e} "
          f"min_bnd_angle={start['min_boundary_angle_over_pi']:.3f}pi "
          f"({start['seconds']} s)", flush=True)

    x1, opt = prob.solve(x0, maxiter=args.maxiter, maxfev=args.maxfev)
    print(f"  [powell    ] area={opt['area']:.4f} cert_viol={opt[ck]:.1e} "
          f"nfev={opt['nfev']} ({opt['seconds']} s)", flush=True)

    t0 = time.time()
    x2, how = prob.polish(x1, x0, tol=args.tol)
    final = {**how, "seconds": round(time.time() - t0, 2)}
    final.update(prob.metrics(x2))
    final.update(prob.audit(x2))
    final.update(prob.corner_cut(x2))
    final["k8_certified"] = bool(final[ck] <= args.tol
                              and final["min_triangle_slack"] >= EPS_TRI - 1e-9)
    print(f"  [polished  ] {how} area={final['area']:.4f} "
          f"A/2pi={final['area_over_2pi']:.4f} cert_viol={final[ck]:.1e} "
          f"audit_viol={final[f'max_violation_audit_k{prob.audit_k}']:.1e} "
          f"corner_lb={final['violation_lower_bound_corner_cut']:.1e} "
          f"k8_certified={final['k8_certified']} ({final['seconds']} s)", flush=True)
    result = {"genus": genus, "mesh": mesh.info, "free_edges": int(prob.free.sum()),
              "feasible_start": start, "powell": opt, "certified": final}
    return result, mesh, prob


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--maxiter", type=int, default=400, help="Powell maxiter")
    ap.add_argument("--maxfev", type=int, default=4000,
                    help="Powell objective-evaluation budget per genus")
    ap.add_argument("--tol", type=float, default=1e-4, help="certified violation target")
    ap.add_argument("--n-boundary", type=int, default=8)
    ap.add_argument("--steiner-k", type=int, default=3)
    ap.add_argument("--certify-k", type=int, default=8)
    ap.add_argument("--audit-k", type=int, default=16)
    ap.add_argument("--genera", type=int, nargs="+", default=[0, 1, 2])
    ap.add_argument("--out", default="benchmarks/genus_search.json")
    args = ap.parse_args()

    t0 = time.time()
    results, flat = [], None
    for g in args.genera:
        res, mesh, prob = explore_genus(g, args)
        results.append(res)
        if g == 0:
            flat = flat_baseline(mesh, prob)
            print(f"  [flat      ] Tutte embedding: area={flat['area']:.4f} "
                  f"(pi={np.pi:.4f}) "
                  f"intrinsic_viol={flat[f'max_violation_intrinsic_k{args.certify_k}']:.3f}")
    out = {
        "description": "Discrete piecewise-flat fillings of S^1 (length 2*pi): minimize "
                       "Heron area over intrinsic edge lengths subject to strict triangle "
                       "inequalities and d(b_i, b_j) >= d_S1(b_i, b_j). Feasible "
                       "hemisphere-profile start, Powell on a penalized objective, radial "
                       "polish to a certified (k = 8) violation <= tol.",
        "config": {**vars(args), "eps_triangle": EPS_TRI, "eps_length": EPS_LEN,
                   "penalty": PENALTY, "barrier": BARRIER},
        "reference": {"pi": np.pi, "two_pi": TWO_PI},
        "flat_baseline_genus0": flat,
        "results": results,
        "total_seconds": round(time.time() - t0, 2),
    }
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).write_text(json.dumps(out, indent=2) + "\n")
    print(f"\nSaved {args.out} ({out['total_seconds']} s)")


if __name__ == "__main__":
    main()

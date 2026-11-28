"""Numerical check of the three-anchor coordinate-pair projection bounds in L^inf_3.

For the equidistant anchors 0, 2pi/3, 4pi/3 the map q_3 = (d(., 0), d(., 2pi/3), d(., 4pi/3))
is 1-Lipschitz into the sup-norm space (``ThreePointEmbedding``). This script checks:

1. each coordinate-pair projection of gamma_3 = q_3 o iota is a simple closed rectangle of
   area 4 pi^2 / 9 (anchor distance phi = 2pi/3, area 2 phi (pi - phi));
2. for a 2-plane P in R^3 with unit normal n, the sup-norm Hausdorff density 4 / lambda(B_P)
   is at least (4/9)(|n_1| + |n_2| + |n_3|), with equality on the diagonal plane, so a
   2-rectifiable image S satisfies mu_H(S) >= (4/9) sum_ij lambda(pi_ij S) >= 16 pi^2 / 27;
3. for arbitrary sets only the constant 1/3 holds (a set of sup-diameter d lies in a cube
   whose three projections have area d^2 each, and the cube itself attains it), giving only
   4 pi^2 / 9 < pi^2 / 2.

Units: Mathlib's unnormalized mu_H^2 (hemisphere = 8).
Usage:  .venv/bin/python3 scripts/three_anchor_projection_check.py
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

TWO_PI = 2 * np.pi


def ball_area(a: np.ndarray, b: np.ndarray) -> float:
    """Lebesgue area of {(s, t) : max_k |s a_k + t b_k| <= 1} (a, b orthonormal)."""
    i, j = np.triu_indices(len(a), 1)
    det = a[i] * b[j] - a[j] * b[i]
    ok = np.abs(det) > 1e-13
    i, j, det = i[ok], j[ok], det[ok]
    pts = []
    for c1, c2 in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
        pts.append(np.c_[(c1 * b[j] - c2 * b[i]) / det, (c2 * a[i] - c1 * a[j]) / det])
    P = np.vstack(pts)
    P = P[np.abs(np.outer(P[:, 0], a) + np.outer(P[:, 1], b)).max(axis=1) <= 1 + 1e-9]
    P = P[np.argsort(np.arctan2(P[:, 1], P[:, 0]))]
    x, y = P[:, 0], P[:, 1]
    return 0.5 * abs(float(np.sum(x * np.roll(y, -1) - np.roll(x, -1) * y)))


def circ(a, b):
    d = np.abs(a - b) % TWO_PI
    return np.minimum(d, TWO_PI - d)


def density_ratio(v):
    n = v / np.linalg.norm(v)
    e = np.eye(3)[np.argmin(np.abs(n))]
    a = np.cross(n, e)
    a /= np.linalg.norm(a)
    b = np.cross(n, a)
    return (4 / ball_area(a, b)) / np.abs(n).sum()


def main():
    th = np.linspace(0, TWO_PI, 360001)[:-1]
    anchors = [0.0, TWO_PI / 3, 2 * TWO_PI / 3]
    pairs = {}
    for i, j in ((0, 1), (1, 2), (2, 0)):
        x, y = circ(th, anchors[i]), circ(th, anchors[j])
        area = 0.5 * abs(float(np.sum(x * np.roll(y, -1) - np.roll(x, -1) * y)))
        distinct = len(np.unique(np.round(np.c_[x, y], 7), axis=0))
        pairs[f"{i}{j}"] = {"shoelace_area": area, "exact": 4 * np.pi**2 / 9,
                            "distinct_samples": distinct, "samples": len(th)}
    rng = np.random.default_rng(0)
    ratios = [minimize(density_ratio, rng.standard_normal(3), method="Nelder-Mead",
                       options={"xatol": 1e-12, "fatol": 1e-14}).fun for _ in range(64)]
    out = {
        "units": "Mathlib unnormalized mu_H^2; hemisphere = 8",
        "pair_projections": pairs,
        "min_density_over_projection_sum": float(min(ratios)),
        "expected_min": 4 / 9,
        "density_at": {"diagonal": density_ratio(np.ones(3)),
                       "coordinate": density_ratio(np.array([0, 0, 1.0])),
                       "edge_diagonal": density_ratio(np.array([1, 1, 0.0]))},
        "bounds": {
            "unconditional_single_projection": 4 * np.pi**2 / 9,
            "unconditional_elementary_sum": (1 / 3) * 3 * 4 * np.pi**2 / 9,
            "rectifiable_sum": (4 / 9) * 3 * 4 * np.pi**2 / 9,
            "sixteen_pi_sq_over_27": 16 * np.pi**2 / 27,
            "pi_sq_over_2": np.pi**2 / 2,
            "n3_linf_ceiling": 5.992840802523578,
            "cone_from_centre_2pi_sq_over_3": 2 * np.pi**2 / 3,
            "sixteen_sqrt3_over_3": 16 * np.sqrt(3) / 3,
            "hemisphere": 8.0,
        },
    }
    print(json.dumps(out, indent=1))
    Path("benchmarks/three_anchor_projection.json").write_text(json.dumps(out, indent=1) + "\n")


if __name__ == "__main__":
    main()

"""Closed-loop invariant & inequality discovery over certified discrete fillings.

Inputs: the 12 certified extremal metrics of ``benchmarks/extremal_discovery.json``
(genus 0-2) plus ``--n-perturb`` strictly feasible random perturbations of them.
Every mesh passes the same certification as ``discover_extremal_metrics.py``
(k = 16 Steiner violation <= 1e-10, exact corner-cut bound 0, triangle slacks,
boundary cone angles >= pi).

Features, per mesh M with vertices V, faces f (areas A_f) and boundary b_0..b_{n-1}:

* Kuratowski matrix ``D[v, j] = d_int(v, b_j)`` (k = 16 Steiner-graph Dijkstra).
* Discrete odd Fourier coefficients ``f_hat[v, m] = (1/n) sum_j D[v, j] e^{-i m theta_j}``.
* Piecewise-linear gradients of every coordinate on every oriented face (unfolded in
  the plane, counter-clockwise), hence Jacobians ``det J_f`` of any pair of
  coordinates: the calibration 2-forms ``dx_i ^ dx_j`` integrated face by face.
* Antipodal excess ``e[v, j] = D[v, j] + D[v, j + n/2] - pi`` and depth
  ``delta = min_j D[v, j]``.

Candidate functionals Phi(M) (59 in four families):

* ``proof-sketch``: oriented calibrations ``|int_M F^* omega|`` for a map F whose
  Lipschitz constant and the comass of omega are both <= 1. By Stokes they depend
  only on boundary data, so they are the same for every filling (a check of the
  pipeline), and ``|int F^* omega| <= Area`` holds for every Riemannian filling.
  They include boundary-pair calibrations ``dx_i ^ dx_j``, Fourier-mode
  calibrations at the repo's Lipschitz constant 1 and at the sharp constant
  ``max_phi mean_j |cos(m theta_j - phi)|`` (= 2/pi in the continuum), Parseval
  (sqrt 2) Kahler sums, and the exact optimum over all weights
  ``sum_{i<j} w_ij dx_i ^ dx_j``: by rotation symmetry it is circulant, its comass
  is exact (spectral bound attained by Fourier phases), and it solves a small LP.
  Repeating that LP with n = 16 .. 2048 boundary points converges to 14 zeta(3)/pi.
* ``mesh-sound-if-1-Lipschitz``: unsigned calibrations, coarea and Dirichlet-type
  integrals that are <= Area when every PL gradient has norm <= 1.
* ``heuristic``: inradius and antipodal-excess functionals with no proof.
* ``control``: constants (4/pi, pi, 7 zeta(3)/pi, pi^2/2, 14 zeta(3)/pi, 2 pi).
  They show what the empirical filter cannot do: every constant <= min Area
  passes it, including 2 pi, which *is* the conjecture.

A functional is empirically sound if ``Phi(M) <= Area(M)`` on every mesh. Sound
functionals are ranked by worst-case tightness ``min_M Phi(M) / Area(M)`` and by
the absolute bound ``min_M Phi(M)``, compared with 4/pi and 14 zeta(3)/pi.

Usage:  .venv/bin/python3 scripts/conjecture_discovery.py --n-perturb 200
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

import numpy as np
from scipy.optimize import linprog, minimize
from scipy.sparse.csgraph import dijkstra
from scipy.special import zeta

sys.path.insert(0, str(Path(__file__).resolve().parent))
from discover_extremal_metrics import GradPathDistance  # noqa: E402
from explore_genus2 import EPS_LEN, FillingProblem, build_mesh  # noqa: E402

FOUR_OVER_PI = 4.0 / np.pi
FOURTEEN_ZETA3_OVER_PI = 14.0 * zeta(3) / np.pi
SEVEN_ZETA3_OVER_PI = 7.0 * zeta(3) / np.pi
ODD_MODES = (1, 3, 5, 7)  # n_b = 16: modes above 8 alias onto these
SOUND_TOL = 1e-9


# ---------------------------------------------------------------------------
# Meshes
# ---------------------------------------------------------------------------


def load_bases(path: str) -> list[dict]:
    runs = json.loads(Path(path).read_text())["runs"]
    return [{"genus": r["genus"], "restart": r["restart"],
             "lengths": np.array(r["final_edge_lengths"])}
            for r in runs if r["final"]["strictly_feasible"]]


def perturb_job(args) -> dict | None:
    """One strictly feasible random perturbation of a certified base metric.

    Free edge lengths get multiplicative log-normal noise of random size sigma;
    feasibility is restored by the rescale/blend bisection of ``FillingProblem``
    (toward the certified base), then fully re-certified.
    """
    base, idx, n_b, tol, seed = args
    rng = np.random.default_rng(seed)
    mesh = build_mesh(base["genus"], n_b=n_b)
    prob = FillingProblem(mesh)
    x_base = base["lengths"][prob.free]
    sigma = float(rng.uniform(0.01, 0.15))
    x = np.maximum(x_base * np.exp(sigma * rng.standard_normal(len(x_base))), EPS_LEN)
    x_new, how = prob.restore(x, x_base, tol)
    cert = prob.certify(x_new, tol)
    if not cert["strictly_feasible"]:
        return None
    return {"genus": base["genus"], "source_restart": base["restart"], "perturbation": idx,
            "sigma": sigma, "restore": how, "lengths": prob.lengths(x_new),
            "certificate": {k: cert[k] for k in ("area", "k16_violation",
                                                 "exact_lower_bound",
                                                 "min_boundary_angle_over_pi")}}


# ---------------------------------------------------------------------------
# Features
# ---------------------------------------------------------------------------


def pl_gradients(mesh, ell: np.ndarray, vals: np.ndarray):
    """Per-face PL gradients of vertex functions ``vals`` (V x K), in face charts.

    Chart of face (A, B, C): A = (0, 0), B = (l_c, 0), C = (x, y), y > 0, so
    coherently oriented faces get coherent (counter-clockwise) charts.
    """
    fe = mesh.face_edges
    la, lb, lc = (ell[fe[:, s]] for s in range(3))
    x = (lb * lb + lc * lc - la * la) / (2 * lc)
    y = np.sqrt(np.maximum(lb * lb - x * x, 1e-24))
    fa, fb, fc = (vals[mesh.faces[:, s]] for s in range(3))
    db, dc = fb - fa, fc - fa
    gx = db / lc[:, None]
    gy = (dc - x[:, None] * gx) / y[:, None]
    return gx, gy, 0.5 * lc * y


def kuratowski_matrix(prob: FillingProblem, ell: np.ndarray) -> np.ndarray:
    pd = prob.cert  # k = 16 Steiner graph
    w, _ = GradPathDistance.segment_geometry(pd, ell)
    g = pd.graph.copy()
    g.data = w[pd.order]
    dist = dijkstra(g, directed=True, indices=pd.bnd)
    return dist[:, :prob.mesh.n_vertices].T  # (V, n_b)


def features(item: dict) -> dict:
    mesh = build_mesh(item["genus"], n_b=item["n_b"])
    prob = FillingProblem(mesh)
    ell = np.asarray(item["lengths"])
    n = len(mesh.boundary)
    D = kuratowski_matrix(prob, ell)
    theta = 2 * np.pi * np.arange(n) / n
    gx, gy, area_f = pl_gradients(mesh, ell, D)
    area = float(area_f.sum())

    # oriented pair calibrations int_M dx_i ^ dx_j (antisymmetric n x n)
    I_pair = (gx * area_f[:, None]).T @ gy - (gy * area_f[:, None]).T @ gx
    # unsigned, averaged over rotations, for each separation s
    unsigned = []
    for s in range(1, n // 2 + 1):
        dets = gx * np.roll(gy, -s, axis=1) - gy * np.roll(gx, -s, axis=1)
        unsigned.append(float((area_f[:, None] * np.abs(dets)).sum(0).mean()))

    # Fourier modes: f_hat[v, m]
    fhat = D @ np.exp(-1j * np.outer(theta, np.arange(n))) / n  # (V, n)
    re_x, re_y, _ = pl_gradients(mesh, ell, fhat.real)
    im_x, im_y, _ = pl_gradients(mesh, ell, fhat.imag)
    det_m = re_x * im_y - re_y * im_x  # (F, n)
    I_mode = (area_f[:, None] * det_m).sum(0)
    hs_m = re_x**2 + re_y**2 + im_x**2 + im_y**2  # |D f_hat_m|_HS^2

    depth = D.min(axis=1)
    dx, dy, _ = pl_gradients(mesh, ell, depth[:, None])
    grad_norm = np.hypot(gx, gy)  # (F, n)
    excess = D + np.roll(D, -n // 2, axis=1) - np.pi  # (V, n)
    excess_f = excess[mesh.faces].mean(axis=1).mean(axis=1)  # per face

    bnd_rows = D[mesh.boundary]
    tent = np.abs(theta[:, None] - theta[None, :]) % (2 * np.pi)
    tent = np.minimum(tent, 2 * np.pi - tent)
    return {
        "genus": item["genus"], "label": item["label"], "area": area,
        "n_b": n, "I_pair": I_pair, "unsigned_pair": unsigned,
        "I_mode": I_mode, "abs_det_mode": (area_f[:, None] * np.abs(det_m)).sum(0),
        "hs_mode_int": (area_f[:, None] * hs_m).sum(0),
        "coarea": float((area_f * np.hypot(dx[:, 0], dy[:, 0])).sum()),
        "dirichlet": float((area_f * (grad_norm**2).mean(1)).sum()),
        "max_grad_int": float((area_f * grad_norm.max(1)).sum()),
        "inradius": float(depth.max()),
        "excess_int": float((area_f * excess_f).sum()),
        "min_excess": float(excess.min()),
        "max_pl_grad": float(grad_norm.max()),
        "area_frac_grad_gt_1": float(area_f[(grad_norm > 1 + 1e-9).any(1)].sum() / area),
        "area_frac_grad_gt_1_05": float(area_f[(grad_norm > 1.05).any(1)].sum() / area),
        "frac_grad_gt_1_05": float((grad_norm > 1.05).mean()),
        "median_pl_grad": float(np.median(grad_norm)),
        "boundary_row_error": float(np.abs(bnd_rows - tent).max()),
    }


# ---------------------------------------------------------------------------
# Calibration search: comass and the exact circulant LP
# ---------------------------------------------------------------------------


def antisym(w: np.ndarray, n: int) -> np.ndarray:
    W = np.zeros((n, n))
    iu = np.triu_indices(n, 1)
    W[iu] = w
    return W - W.T


def comass_estimate(W: np.ndarray, rng: np.random.Generator, starts: int = 64):
    """max over unit planar vectors g_i of sum_{i<j} W_ij (g_i x g_j).

    The 2-form is multilinear in each g_i, so the max over the unit disk is on the
    circle: maximize ``F(phi) = sum_{i<j} W_ij sin(phi_j - phi_i)`` by multi-start
    L-BFGS. This is a lower estimate of the comass. ``spectral`` is a sound upper
    bound: ``F = z^* H z / 2 <= n lambda_max(H) / 2`` with ``H = -i W``, ``|z_i| = 1``.
    """
    n = len(W)

    def f(phi):
        s = np.sin(phi[None, :] - phi[:, None])
        c = np.cos(phi[None, :] - phi[:, None])
        val = 0.5 * (W * s).sum()
        grad = (W * c).sum(0)  # dF/dphi_k = sum_i W_ik cos(phi_k - phi_i)
        return -val, -grad

    best, best_phi = -np.inf, None
    for _ in range(starts):
        res = minimize(f, rng.uniform(0, 2 * np.pi, n), jac=True, method="L-BFGS-B")
        if -res.fun > best:
            best, best_phi = -res.fun, res.x
    spectral = 0.5 * n * float(np.linalg.eigvalsh(-1j * W).max())
    return float(best), best_phi, spectral


def circulant_from(a: np.ndarray, n: int) -> np.ndarray:
    """Antisymmetric circulant W_ij = a_{(j - i) mod n}, a_{n-s} = -a_s, a_0 = a_{n/2} = 0."""
    full = np.zeros(n)
    h = n // 2
    full[1:h] = a
    full[h + 1:] = -a[::-1]
    idx = (np.arange(n)[None, :] - np.arange(n)[:, None]) % n
    return full[idx]


def calibration_lp(J: np.ndarray, n: int) -> dict:
    """Exact optimum of <w, I> / comass(w) over all constant-coefficient 2-forms.

    The boundary invariant I_ij = J_{(j-i) mod n} is rotation invariant and the
    comass is a rotation-invariant norm, so averaging any w over rotations keeps
    <w, I> and does not increase the comass: the optimum is circulant. For a
    circulant W the eigenvectors of H = -i W are the Fourier modes
    z_j = e^{i m theta_j}, which have unit modulus, so the spectral upper bound
    is attained and comass(W) = n max_m sum_s a_s sin(2 pi m s / n) exactly.
    With <w, I> = n sum_s a_s J_s this is the LP

        maximize sum_s a_s J_s  s.t.  |sum_s a_s sin(2 pi m s / n)| <= 1,  m = 1..n/2-1.
    """
    h = n // 2
    s_idx = np.arange(1, h)
    S = np.sin(2 * np.pi * np.outer(s_idx, s_idx) / n)
    res = linprog(-J[1:h], A_ub=np.vstack([S, -S]), b_ub=np.ones(2 * len(S)),
                  bounds=[(None, None)] * (h - 1), method="highs")
    a = res.x
    return {"n": n, "value": float(-res.fun), "a": a.tolist()}


def calibration_search(I: np.ndarray, seed: int = 0) -> dict:
    """Exact circulant LP, then an independent check of the comass of the optimum."""
    n = len(I)
    lp = calibration_lp(I[0], n)
    W = circulant_from(np.array(lp["a"]), n)
    iu = np.triu_indices(n, 1)
    cm, _, spectral = comass_estimate(W, np.random.default_rng(seed), starts=256)
    pairing = abs(float(I[iu] @ W[iu]))
    return {"value": pairing / spectral, "sound_value_spectral": pairing / spectral,
            "comass_estimate": cm, "comass_spectral_bound": spectral,
            "lp_value": lp["value"], "a": lp["a"], "w": W[iu].tolist()}


def fixed_form_value(I: np.ndarray, w: np.ndarray, seed: int = 1) -> dict:
    n = len(I)
    iu = np.triu_indices(n, 1)
    cm, _, spectral = comass_estimate(antisym(w, n), np.random.default_rng(seed), 256)
    val = abs(float(I[iu] @ w))
    return {"value": val / cm, "sound_value_spectral": val / spectral, "comass_estimate": cm}


# ---------------------------------------------------------------------------
# Functional library
# ---------------------------------------------------------------------------


def sharp_lipschitz(n: int, m: int) -> float:
    """max_phi (1/n) sum_j |cos(m theta_j - phi)|: Lipschitz constant of f_hat_m."""
    theta = 2 * np.pi * np.arange(n) / n
    phis = np.linspace(0, 2 * np.pi, 20001)
    return float(np.abs(np.cos(m * theta[None, :] - phis[:, None])).mean(1).max())


def build_library(n: int, calib: dict) -> list[dict]:
    """Each entry: name, family, status, formula, fn(features) -> Phi."""
    lib = []

    def add(name, family, status, formula, fn):
        lib.append({"name": name, "family": family, "status": status,
                    "formula": formula, "fn": fn})

    P, MS, H, C = "proof-sketch", "mesh-sound-if-1-Lipschitz", "heuristic", "control"
    for s in range(1, n // 2 + 1):
        add(f"pair_calibration_s{s}", "boundary-pair calibration", P,
            f"|int_M dx_0 ^ dx_{s}|, x_j = d(., b_j); comass 1 for 1-Lipschitz x_j",
            lambda F, s=s: abs(F["I_pair"][0, s]))
    for m in ODD_MODES:
        add(f"fourier_mode{m}_lip1", "Fourier-mode calibration", P,
            f"|int_M det D f_hat_{m}| (Lipschitz 1, as in UniversalAreaBound)",
            lambda F, m=m: abs(F["I_mode"][m]))
        L = sharp_lipschitz(n, m)
        add(f"fourier_mode{m}_sharp_lip", "Fourier-mode calibration", P,
            f"|int_M det D f_hat_{m}| / L^2, L = max_phi mean|cos(m theta - phi)| = {L:.4f}",
            lambda F, m=m, L=L: abs(F["I_mode"][m]) / L**2)
    weights = {"flat": lambda m: 1.0, "inv_m": lambda m: 1.0 / m,
               "inv_m2": lambda m: 1.0 / m**2}
    for wname, wf in weights.items():
        for top in (3, 5, 7):
            ms = [m for m in ODD_MODES if m <= top]
            add(f"kahler_{wname}_upto{top}", "Parseval Kahler sum", P,
                f"2 sum_{{m odd <= {top}}} w_m |I_m| / max w, w_m = {wname}; "
                "sqrt2 (f_hat_m)_m is 1-Lipschitz into l2",
                lambda F, ms=ms, wf=wf: 2 * sum(wf(m) * abs(F["I_mode"][m]) for m in ms)
                / max(wf(m) for m in ms))
    best = max(calib["refine"], key=lambda r: r["n"])
    add(f"calibration_lp_n{best['n']}", "weighted pair calibration", P,
        f"exact LP optimum with {best['n']} boundary points (boundary-only; same "
        "value for every filling, not evaluated face by face)",
        lambda F, v=best["value"]: v)
    add("kahler_flat_upto1", "Parseval Kahler sum", P, "2 |I_1|",
        lambda F: 2 * abs(F["I_mode"][1]))
    for key, desc in (("lp", "exact optimum over all w_ij (circulant LP)"),
                      ("sign", "w_ij = sign(I_ij)"), ("self", "w_ij = I_ij")):
        add(f"calibration_{key}", "weighted pair calibration", P,
            f"|sum w_ij int dx_i ^ dx_j| / comass(w), {desc}",
            lambda F, key=key: calib[key]["value"] * F["calib_scale"])

    for s in range(1, n // 2 + 1):
        add(f"unsigned_pair_s{s}", "unsigned calibration", MS,
            f"mean_i int_M |dx_i ^ dx_(i+{s})|",
            lambda F, s=s: F["unsigned_pair"][s - 1])
    add("unsigned_fourier1_sharp", "unsigned calibration", MS,
        "int_M |det D f_hat_1| / L_1^2",
        lambda F: F["abs_det_mode"][1] / sharp_lipschitz(n, 1) ** 2)
    add("coarea_depth", "coarea", MS, "int_M |grad delta|, delta = min_j d(., b_j)",
        lambda F: F["coarea"])
    add("max_gradient", "coarea", MS, "int_M max_j |grad x_j|", lambda F: F["max_grad_int"])
    for cst in (0.9, 1.0, 1.1):
        add(f"kuratowski_dirichlet_{cst}", "Kuratowski Dirichlet energy",
            MS if cst <= 1.0 else H, f"{cst} * int_M mean_j |grad x_j|^2",
            lambda F, cst=cst: cst * F["dirichlet"])
    add("fourier_hs_energy", "spectral Dirichlet energy", MS,
        "int_M |D (sqrt2 f_hat_m)_{m=1..7}|_HS^2 / 2",
        lambda F: float(sum(2 * F["hs_mode_int"][m] for m in range(1, 8)) / 2))
    add("fourier1_hs_energy", "spectral Dirichlet energy", MS,
        "int_M |D f_hat_1|_HS^2 / (2 L_1^2)",
        lambda F: F["hs_mode_int"][1] / (2 * sharp_lipschitz(n, 1) ** 2))

    for cst, cname in ((2.0, "2"), (np.pi, "pi"), (8 / np.pi, "8/pi"), (4.0, "4")):
        add(f"inradius_sq_{cname}", "inradius", H, f"{cname} * (max_v min_j d(v, b_j))^2",
            lambda F, cst=cst: cst * F["inradius"] ** 2)
    for cst in (1.0, 2.0, 4.0):
        add(f"antipodal_excess_{cst:g}", "antipodal excess", H,
            f"{cst:g} * int_M mean_j (d(., b_j) + d(., b_j+n/2) - pi)",
            lambda F, cst=cst: cst * F["excess_int"])

    for val, cname in ((FOUR_OVER_PI, "4/pi"), (np.pi, "pi"),
                       (SEVEN_ZETA3_OVER_PI, "7 zeta(3)/pi"), (np.pi**2 / 2, "pi^2/2"),
                       (FOURTEEN_ZETA3_OVER_PI, "14 zeta(3)/pi"), (2 * np.pi, "2 pi")):
        add(f"constant_{cname.replace(' ', '')}", "constant", C, f"Phi = {cname}",
            lambda F, val=val: float(val))
    return lib


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------


def continuum_pair_invariants(n: int) -> np.ndarray:
    """int over the boundary of x_i dx_j for the exact tent profiles (PL, exact)."""
    theta = 2 * np.pi * np.arange(n) / n
    X = np.abs(theta[:, None] - theta[None, :]) % (2 * np.pi)
    X = np.minimum(X, 2 * np.pi - X)
    Xn = np.roll(X, -1, axis=0)
    return 0.5 * ((X + Xn).T @ (Xn - X))


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--input", default="benchmarks/extremal_discovery.json")
    ap.add_argument("--n-perturb", type=int, default=200)
    ap.add_argument("--strict-tol", type=float, default=1e-10)
    ap.add_argument("--refine", type=int, nargs="+",
                    default=[16, 32, 64, 128, 256, 512, 1024, 2048],
                    help="boundary sample counts for the boundary-only calibration LP")
    ap.add_argument("--workers", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--seed", type=int, default=2026)
    ap.add_argument("--out", default="benchmarks/conjecture_discovery.json")
    args = ap.parse_args()
    t0 = time.time()

    bases = load_bases(args.input)
    n_b = int(json.loads(Path(args.input).read_text())["config"]["n_boundary"])
    print(f"{len(bases)} certified base meshes", flush=True)

    # 1. strictly feasible perturbations (oversample, keep the first n_perturb)
    rng = np.random.default_rng(args.seed)
    jobs = [(bases[i % len(bases)], i, n_b, args.strict_tol, int(rng.integers(2**31)))
            for i in range(int(1.25 * args.n_perturb) + 8)]
    with ProcessPoolExecutor(args.workers) as ex:
        perturbed = [p for p in ex.map(perturb_job, jobs, chunksize=2) if p is not None]
    n_attempted = len(jobs)
    perturbed = perturbed[:args.n_perturb]
    print(f"{len(perturbed)} strictly feasible perturbations "
          f"({n_attempted} attempted, {time.time() - t0:.0f} s)", flush=True)

    items = [{"genus": b["genus"], "lengths": b["lengths"], "n_b": n_b,
              "label": f"extremal g{b['genus']} r{b['restart']}"} for b in bases]
    items += [{"genus": p["genus"], "lengths": p["lengths"], "n_b": n_b,
               "label": f"perturb {p['perturbation']} of g{p['genus']} "
                        f"r{p['source_restart']} (sigma {p['sigma']:.3f})"}
              for p in perturbed]

    # 2. features
    with ProcessPoolExecutor(args.workers) as ex:
        feats = list(ex.map(features, items, chunksize=4))
    print(f"features for {len(feats)} meshes ({time.time() - t0:.0f} s)", flush=True)

    # pipeline checks: boundary rows of D, Stokes for the pair calibrations
    I_cont = continuum_pair_invariants(n_b)
    stokes_err = max(float(np.abs(np.abs(F["I_pair"]) - np.abs(I_cont)).max()) for F in feats)
    bnd_err = max(F["boundary_row_error"] for F in feats)
    sign = np.sign(feats[0]["I_pair"][0, 4] / I_cont[0, 4])
    print(f"Stokes check: max | |I_face| - |I_boundary| | = {stokes_err:.2e}; "
          f"boundary-row error {bnd_err:.2e}", flush=True)

    # 3. closed-loop calibration search on the (mesh-independent) boundary invariant
    I_ref = sign * I_cont
    iu = np.triu_indices(n_b, 1)
    calib = {"lp": calibration_search(I_ref, seed=args.seed),
             "sign": fixed_form_value(I_ref, np.sign(I_ref[iu])),
             "self": fixed_form_value(I_ref, I_ref[iu])}
    for k, v in calib.items():
        print(f"calibration {k}: {v['value']:.6f} (spectral-sound {v['sound_value_spectral']:.4f})",
              flush=True)
    # boundary-only refinement: the same exact LP with n boundary points
    refine = [calibration_lp(continuum_pair_invariants(n)[0], n) for n in args.refine]
    for r in refine:
        r.pop("a")
    for a, b in zip(refine, refine[1:]):  # Richardson, error O(1/n^2)
        b["richardson"] = b["value"] + (b["value"] - a["value"]) / 3
    print("boundary refinement: " + ", ".join(f"n={r['n']}: {r['value']:.7f}" for r in refine),
          flush=True)
    calib["refine"] = refine
    # per-mesh scale: |<w, I_mesh>| / |<w, I_ref>| (1 up to Stokes roundoff)
    for F in feats:
        w = np.array(calib["lp"]["w"])
        F["calib_scale"] = abs(F["I_pair"][iu] @ w) / abs(I_ref[iu] @ w)

    # 4. evaluate and rank
    lib = build_library(n_b, calib)
    areas = np.array([F["area"] for F in feats])
    results = []
    for fn in lib:
        vals = np.array([fn["fn"](F) for F in feats])
        ratio = vals / areas
        viol = int((vals > areas * (1 + SOUND_TOL)).sum())
        worst = int(np.argmin(ratio))
        results.append({
            "name": fn["name"], "family": fn["family"], "status": fn["status"],
            "formula": fn["formula"], "violations": viol, "sound_empirically": viol == 0,
            "min_ratio": float(ratio.min()), "max_ratio": float(ratio.max()),
            "worst_mesh": feats[worst]["label"], "min_value": float(vals.min()),
            "max_value": float(vals.max()),
            "min_value_over_4_over_pi": float(vals.min() / FOUR_OVER_PI),
            "min_value_over_14zeta3_over_pi": float(vals.min() / FOURTEEN_ZETA3_OVER_PI),
            "constant_across_meshes": bool(np.ptp(vals) <= 1e-6 * max(1.0, abs(vals).max())),
        })
    sound = sorted((r for r in results if r["sound_empirically"]),
                   key=lambda r: (-r["min_ratio"], -r["min_value"]))
    for rank, r in enumerate(sound, 1):
        r["rank_tightness"] = rank
    proved = sorted((r for r in sound if r["status"] == "proof-sketch"),
                    key=lambda r: -r["min_value"])
    print(f"\n{len(lib)} functionals, {len(sound)} empirically sound, "
          f"{len(results) - len(sound)} violated")
    print("top proof-sketch bounds:")
    for r in proved[:6]:
        print(f"  {r['name']:28s} min Phi = {r['min_value']:.4f} "
              f"(x {r['min_value_over_4_over_pi']:.3f} of 4/pi), "
              f"tightness {r['min_ratio']:.3f}")

    by_genus = {}
    for g in sorted({F["genus"] for F in feats}):
        a = areas[[F["genus"] == g for F in feats]]
        by_genus[str(g)] = {"meshes": int(len(a)), "min_area": float(a.min()),
                            "max_area": float(a.max())}
    out = {
        "description": "Closed-loop invariant & inequality discovery over certified "
                       "discrete fillings (12 extremal metrics + strictly feasible "
                       "perturbations, genus 0-2).",
        "config": vars(args),
        "reference": {"four_over_pi": FOUR_OVER_PI, "pi": np.pi,
                      "seven_zeta3_over_pi": SEVEN_ZETA3_OVER_PI,
                      "pi_sq_over_2": np.pi**2 / 2,
                      "fourteen_zeta3_over_pi": FOURTEEN_ZETA3_OVER_PI, "two_pi": 2 * np.pi},
        "meshes": {"extremal": len(bases), "perturbed": len(perturbed),
                   "perturbations_attempted": n_attempted, "by_genus": by_genus},
        "checks": {
            "stokes_max_abs_error": stokes_err,
            "boundary_row_max_error": bnd_err,
            "max_pl_gradient_norm": max(F["max_pl_grad"] for F in feats),
            "max_area_fraction_with_pl_gradient_gt_1":
                max(F["area_frac_grad_gt_1"] for F in feats),
            "mean_area_fraction_with_pl_gradient_gt_1_05":
                float(np.mean([F["area_frac_grad_gt_1_05"] for F in feats])),
            "mean_fraction_of_face_coordinate_gradients_gt_1_05":
                float(np.mean([F["frac_grad_gt_1_05"] for F in feats])),
            "median_pl_gradient_norm": float(np.median([F["median_pl_grad"] for F in feats])),
            "min_antipodal_excess": min(F["min_excess"] for F in feats),
        },
        "continuum_pair_invariants_row0": I_cont[0].tolist(),
        "sharp_fourier_lipschitz": {str(m): sharp_lipschitz(n_b, m) for m in ODD_MODES},
        "calibration_search": calib,
        "ranking_empirically_sound": [r["name"] for r in sound],
        "ranking_proof_sketch_by_bound": [r["name"] for r in proved],
        "functionals": results,
        "per_mesh": [{"label": F["label"], "genus": F["genus"], "area": F["area"],
                      "inradius": F["inradius"], "coarea": F["coarea"],
                      "dirichlet": F["dirichlet"], "max_pl_grad": F["max_pl_grad"]}
                     for F in feats],
        "perturbations": [{k: v for k, v in p.items() if k != "lengths"} for p in perturbed],
        "total_seconds": round(time.time() - t0, 2),
    }
    Path(args.out).write_text(json.dumps(out, indent=2) + "\n")
    print(f"\nSaved {args.out} ({out['total_seconds']} s)")


if __name__ == "__main__":
    main()

# Gromov's Filling Area Conjecture — A Neuro-Symbolic Lean 4 Formalization

[![Lean CI](https://github.com/MonodeepMukherjee/gromov_filling_area/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/MonodeepMukherjee/gromov_filling_area/actions/workflows/lean_action_ci.yml)
![Lean](https://img.shields.io/badge/Lean-v4.36.0-blue)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.36.0-blue)
![sorry](https://img.shields.io/badge/sorry-0-brightgreen)
![axioms](https://img.shields.io/badge/custom%20axioms-0-brightgreen)

A machine-checked Lean 4 + Mathlib formalization effort for **Gromov's Filling Area
Conjecture**. An LLM agent writes the proofs, and the Lean kernel checks every step
before anything is accepted.

---

## Project Overview

### The conjecture

Take the Riemannian circle `S¹` of length `2π`. A compact surface `M` with boundary
`∂M = S¹` is an **isometric filling** if, for any two boundary points, the
distance measured *through* `M` equals their distance *along* the circle. So the
filling offers no shortcuts.

> **Gromov's Filling Area Conjecture (1983).** Every orientable isometric filling of
> the circle of length `2π` has area at least `2π`, the area of the round
> hemisphere.

The conjecture is a central open problem in systolic geometry. It has been proved
for fillings of genus 0 (Pu, Ivanov) and genus 1 (Bangert–Croke–Ivanov–Katz), but
it is still open in general.

### What this repository formalizes

| Layer | Content |
| :--- | :--- |
| **Statement** | `Circle2Pi := AddCircle (2π)`, the `IsometricFilling` structure, and `GromovFillingAreaConjecture` stated with the 2-dimensional Hausdorff measure. |
| **Kuratowski profile** | The distance profile `f_x(θ) = dist x (ι θ)` of an interior point, which is 1-Lipschitz in `θ` and non-expansive in `x`. |
| **Harmonic-analysis setup** | `f_x` lifted to a `2π`-periodic, 1-Lipschitz function on `ℝ`, so that Fourier and Wirtinger arguments can be applied. |
| **Antipodal geometry** | `f_x(θ) + f_x(θ + π) ≥ dist(θ, θ + π)`, the exact antipodal distance `dist(θ, θ + π) = π`, and the sharp bound `max(f_x(θ), f_x(θ + π)) ≥ π/2`. In words, every interior point is at distance at least `π/2` from one of any two antipodal boundary points. |
| **Number theory** | `Re ζ(3) = ∑ 1/n³`, the even/odd split `∑_{odd} 1/n³ = (7/8)·ζ(3)`, and positivity of the target constant `14·ζ(3)/π`. |

> **Scope.** The conjecture is *stated*, not proved. Every lemma listed below is
> fully kernel-checked. The surface/orientability condition in `IsometricFilling` is
> currently an abstract `Prop` field, and replacing it with a genuine
> topological-surface structure is planned future work.

---

## Neuro-Symbolic Architecture

The proofs come from an LLM agent (Claude) working **inside a compiler-in-the-loop
harness**. The neural side proposes tactics and lemma decompositions. The symbolic
side (the Lean 4 kernel and Mathlib) is the only judge of correctness. A proof
counts as done only when it compiles, so a confident-sounding but wrong proof
cannot get through.

```
                ┌──────────────────────────────────────────────┐
                │  CLAUDE.md  — agent protocol / system policy  │
                │  • run verifier after EVERY .lean edit         │
                │  • no `axiom`, no `admit`, no `sorry`          │
                │  • `module` + `@[expose] public section`       │
                │  • ≤100-char lines; small reusable lemmas      │
                └───────────────────────┬──────────────────────┘
                                        │ constrains
                                        ▼
   ┌───────────────┐   edit .lean   ┌──────────────────────────┐
   │  LLM prover   │ ─────────────▶ │ scripts/verify_and_log.py │
   │  (Claude)     │                │  `lake build <Module>`    │
   │               │ ◀───────────── │  detect errors / `sorry`  │
   └───────────────┘  [PASS]/[FAIL] └─────────────┬────────────┘
         ▲            + error tail                │ append record
         │                                        ▼
         │                         ┌──────────────────────────────┐
         └──── repair loop ─────── │ benchmarks/results.jsonl      │
                                   │ {timestamp, model, module,    │
                                   │  success, has_sorry,          │
                                   │  compile_ms, error_tail}      │
                                   └─────────────┬────────────────┘
                                                 │ aggregate
                                                 ▼
                                   ┌──────────────────────────────┐
                                   │ scripts/generate_report.py    │
                                   │ → Markdown benchmark table    │
                                   └──────────────────────────────┘
```

### Components

1. **`CLAUDE.md` (protocol layer).** A machine-readable policy that the agent loads
   at session start. It requires the verifier to run after every edit, bans
   `axiom`/`admit`, enforces Mathlib style (100-character lines, the `module`
   system, `@[expose] public section`), and tells the agent to split hard geometric
   steps into small helper lemmas. This keeps each search step small enough for an
   LLM to handle.

2. **`scripts/verify_and_log.py` (symbolic oracle).** Runs `lake build <Module>`,
   records the wall-clock compile time, and marks a run as failed if it returns a
   non-zero exit code *or* any `declaration uses 'sorry'` warning. A failing run
   prints the full compiler output so the agent can repair the proof from the real
   type-checker diagnostics.

3. **`benchmarks/results.jsonl` (telemetry).** An append-only log with one JSON
   record per verification attempt: timestamp, model tag, module, success flag,
   `sorry` flag, compile latency, and the last 800 characters of the error output
   on failure. It shows how many attempts each proof took and what the failures
   looked like.

4. **`scripts/generate_report.py` (reporting).** Groups the log by module and
   outputs the benchmark table below.

5. **Lean Action CI.** `.github/workflows/lean_action_ci.yml` rebuilds the whole
   library with `leanprover/lean-action` on every push and pull request, and builds
   API docs with `docgen-action`. This gives an independent, reproducible check on
   top of the local loop.

### Example repair trace

The log contains a real repair. The first attempt at
`periodicDistance_lipschitz` failed with:

```
Type mismatch: After simplification, term
  LipschitzWith.comp (kuratowskiMap_lipschitzWith F x) circle2Pi_coe_lipschitz
 has type  LipschitzWith 1 (kuratowskiMap F x ∘ fun t ↦ ↑t)
but is expected to have type  LipschitzWith 1 (periodicDistance F x)
```

From that diagnostic, the agent changed the proof to build the composite as a
`have` and close the goal with `rwa [one_mul] at h`. Lean unfolds
`periodicDistance` to the composite by definitional unfolding. The next build passed
in 34.5 s.

---

## Benchmark & Verification Table

Generated by `python3 scripts/generate_report.py` from `benchmarks/results.jsonl`:

| Lean 4 Module | Attempts | Final Status | Avg Compile (ms) | Best Compile (ms) |
| :--- | :---: | :---: | :---: | :---: |
| `GromovFillingArea.Kuratowski` | 1 | **PASS (0 sorry)** | 51830.1 ms | 51830.1 ms |
| `GromovFillingArea.FourierBound` | 2 | **PASS (0 sorry)** | 40355.4 ms | 34459.6 ms |
| `GromovFillingArea.ZetaBound` | 1 | **PASS (0 sorry)** | 52180.5 ms | 52180.5 ms |
| `GromovFillingArea.FourierEnergy` | 1 | **PASS (0 sorry)** | 45623.9 ms | 45623.9 ms |
| `GromovFillingArea` | 6 | **PASS (0 sorry)** | 50427.7 ms | 35848.5 ms |
| `GromovFillingArea.Witness` | 1 | **PASS (0 sorry)** | 53272.0 ms | 53272.0 ms |
| `GromovFillingArea.AntipodalRadius` | 1 | **PASS (0 sorry)** | 57994.9 ms | 57994.9 ms |
| `GromovFillingArea.L2Energy` | 1 | **PASS (0 sorry)** | 70202.1 ms | 70202.1 ms |
| `GromovFillingArea.IntegralBound` | 2 | **PASS (0 sorry)** | 70766.6 ms | 85030.9 ms |
| `GromovFillingArea.ParsevalEnergy` | 2 | **PASS (0 sorry)** | 48838.1 ms | 44006.3 ms |

**Summary:** 10 build targets, 18 logged verification attempts, 10/10 passing. Three
attempts failed and were repaired from the compiler diagnostics:

- The first `FourierBound` build failed with a type mismatch.
- The first `IntegralBound` build used the unknown identifier `continuous_add_right`.
  It was fixed by switching to `continuous_id.add continuous_const`.
- The first `ParsevalEnergy` build failed because `haarAddCircle` lives in the
  `AddCircle` namespace. It was fixed by adding `open AddCircle`. The root `GromovFillingArea`
target was re-verified each time a new module was exported. Compile times include the `lake build` of each
module's dependency chain on a local machine. `Basic` is checked as a dependency of
every target.

---

## Verified Declarations Index

All 26 theorems below are kernel-checked, with no `sorry`, no `admit`, and no
custom `axiom`.

### `GromovFillingArea.Basic` — problem statement

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `Circle2Pi` | `abbrev` | `AddCircle (2 * π)`, the Riemannian circle of length `2π` |
| `IsometricFilling` | `structure` | Compact metric `M` with an isometric embedding `ι : Circle2Pi → M` |
| `GromovFillingAreaConjecture` | `def` (Prop) | `∀ M, Nonempty (IsometricFilling M) → 2π ≤ μH[2] univ` |
| `two_pi_pos` | theorem | `0 < 2 * π` (non-triviality sanity check) |

### `GromovFillingArea.Kuratowski` — distance profiles

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `kuratowskiMap` | `def` | `kuratowskiMap F x θ = dist x (F.ι θ)` |
| `kuratowski_lipschitz` | theorem | `\|f_x θ₁ − f_x θ₂\| ≤ dist θ₁ θ₂` |
| `kuratowski_nonexpansive` | theorem | `\|f_x θ − f_y θ\| ≤ dist x y` |

### `GromovFillingArea.FourierBound` — periodic lift

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `periodicDistance` | `def` | `t ↦ kuratowskiMap F x (t : Circle2Pi)` on `ℝ` |
| `periodicDistance_periodic` | theorem | `Function.Periodic (periodicDistance F x) (2π)` |
| `circle2Pi_coe_lipschitz` | theorem | The quotient map `ℝ → Circle2Pi` is `LipschitzWith 1` |
| `kuratowskiMap_lipschitzWith` | theorem | `LipschitzWith 1 (kuratowskiMap F x)` |
| `periodicDistance_lipschitz` | theorem | `LipschitzWith 1 (periodicDistance F x)` |

### `GromovFillingArea.ZetaBound` — antipodal bound & ζ(3) series

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `kuratowski_antipodal_sum` | theorem | `dist θ (θ + π) ≤ f_x θ + f_x (θ + π)` |
| `tsum_even_inv_cube` | theorem | `∑' k, 1/(2k)³ = (1/8) · ∑' n, 1/n³` |
| `riemannZeta_three_re` | theorem | `(ζ 3).re = ∑' n, 1/n³` |
| `tsum_odd_inv_cube` | theorem | `∑' k, 1/(2k+1)³ = (7/8) · (ζ 3).re` |

### `GromovFillingArea.FourierEnergy` — quantitative constant

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `fourier_constant_pos` | theorem | `0 < 14 · (ζ 3).re / π` |
| `kuratowski_antipodal_max` | theorem | `(1/2) · dist θ (θ + π) ≤ max (f_x θ) (f_x (θ + π))` |

### `GromovFillingArea.Witness` — non-vacuity witnesses

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `circle2Pi_self_isometry` | theorem | `Isometry (id : Circle2Pi → Circle2Pi)` (via `isometry_id`) |
| `circle2Pi_dist_le_pi` | theorem | `dist θ₁ θ₂ ≤ π` on `Circle2Pi` (via `AddCircle.norm_le_half_period`) |

### `GromovFillingArea.AntipodalRadius` — sharp antipodal radius bound

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `circle2Pi_dist_add_pi` | theorem | `dist θ (θ + π) = π` (via `AddCircle.norm_half_period_eq`) |
| `kuratowski_half_pi_bound` | theorem | `π / 2 ≤ max (f_x θ) (f_x (θ + π))` for every `x : M`, `θ` |

### `GromovFillingArea.L2Energy` — squared antipodal energy & continuity

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `kuratowski_antipodal_sq_sum` | theorem | `π² / 2 ≤ (f_x θ)² + (f_x (θ + π))²` |
| `periodicDistance_continuous` | theorem | `Continuous (periodicDistance F x)` (from the 1-Lipschitz bound) |

### `GromovFillingArea.IntegralBound` — global L² energy lower bound

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `periodicDistance_sq_intervalIntegrable` | theorem | `t ↦ f(t)²` is interval-integrable on every `[a, b]` |
| `periodicDistance_antipodal_sq_sum` | theorem | `π² / 2 ≤ f(t)² + f(t + π)²` for the real lift (helper) |
| `periodicDistance_sq_integral_shift` | theorem | `∫₀^π f(t + π)² dt = ∫_π^{2π} f(t)² dt` (helper) |
| `periodicDistance_l2_lower_bound` | theorem | `π³ / 2 ≤ ∫₀^{2π} f(t)² dt` for every interior point `x : M` |

### `GromovFillingArea.ParsevalEnergy` — Parseval identity for distance profiles

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `Circle2Pi.fact_two_pi_pos` | `instance` | `Fact (0 < 2π)`, required by `haarAddCircle` on `Circle2Pi` |
| `kuratowskiComplex` | `def` | `θ ↦ (kuratowskiMap F x θ : ℂ)`, the complexified profile |
| `kuratowskiComplex_continuous` | theorem | `Continuous (kuratowskiComplex F x)` (helper) |
| `kuratowskiComplex_memLp` | theorem | `MemLp (kuratowskiComplex F x) 2 haarAddCircle` |
| `kuratowski_parseval_hasSum` | theorem | `HasSum (n ↦ ‖f̂ n‖²) (∫ ‖kuratowskiComplex F x θ‖² ∂haarAddCircle)` |

---

## Numerical Exploration (Genus 0–2)

`scripts/explore_genus2.py` is a small numerical side experiment that runs next to
the formal proofs. It builds orientable simplicial triangulations of genus
`g ∈ {0, 1, 2}` with one boundary cycle of `n_b = 8` vertices. These come from an
octahedron or from connected sums of 7-vertex tori, with one face punched out, one
midpoint subdivision, and a boundary collar. Each mesh is checked for `χ = 1 − 2g`,
coherent orientation, manifold vertex links, and a single boundary cycle.

The metric is given by **intrinsic edge lengths**, a piecewise-flat Riemannian
metric with no embedding. Boundary edges are fixed at `2π/n_b`, so `∂M` has length
exactly `2π`. COBYLA (`maxiter=80`, 2 random restarts per phase) minimizes the
total Heron area subject to:

- strict triangle inequalities `ℓ_a + ℓ_b − ℓ_c ≥ 10⁻³` on every face, and
- the isometric boundary condition `d(b_i, b_j) ≥ d_{S¹}(b_i, b_j)`, where
  `d` is computed with `scipy.sparse.csgraph.shortest_path`.

There are two choices of `d`:

- **Phase 1, edge graph:** paths that run only along mesh edges.
- **Phase 2, intrinsic:** a Steiner graph with 3 points per edge, plus straight
  segments inside each face unfolded in the plane.

Every result is re-certified with a finer Steiner graph (8 points per edge). That
graph gives an upper bound on the true geodesic distance, so any violation it
reports is real.

Results (`benchmarks/genus_search.json`, total runtime ≈ 8 s on an M1):

| Filling | Area | `A / 2π` | Median fatness `2r/R` | Certified violation (k = 8) |
| :--- | :---: | :---: | :---: | :---: |
| g = 0, flat Tutte embedding in ℝ² | 2.98 | 0.47 | — | **1.09** |
| g = 0, edge-graph constraint (best) | 7.98 | 1.27 | 0.003 | **1.84** |
| g = 0, intrinsic constraint (best) | 26.72 | 4.25 | 0.68 | 0.026 |
| g = 1, edge-graph constraint (best) | 42.56 | 6.77 | 0.44 | 0.258 |
| g = 1, intrinsic constraint (best) | 41.72 | 6.64 | 0.44 | 0.031 |
| g = 2, both phases | — | — | — | no feasible run (≥ 0.74) |

### Why flat fillings fail

A flat disk whose boundary has length `2π` has area about `π`. Here the Tutte
embedding gives `2.98`, and `π` is the isoperimetric maximum. The disk is too
small to be an isometric filling, though. Antipodal boundary points are joined by
a straight chord of length `≈ 2.05`, but the boundary arc between them has length
`π ≈ 3.14`, so the isometric condition is violated by `≈ 1.09`. To satisfy
`d ≥ d_{S¹}`, a filling must bulge out of the plane. The round hemisphere does
this with area exactly `2π ≈ 6.283`, and the conjecture says nothing smaller is
possible.

### Why the edge-graph constraint is not enough

Under the edge-graph constraint, the optimizer satisfies every constraint with
**needle triangles**. The median fatness is `0.003`, every face sits on its
triangle-inequality margin, and the area is `7.98`. The edge-graph distance never
lets a path cut across a face, so it overestimates the true intrinsic distance.
The certified check shows that real geodesics shortcut through the collapsed
faces, with a violation of `1.84`. This relaxation cannot tell you anything about
the true filling area.

### What this run does and does not show

- With the Steiner (intrinsic) constraint, the needle exploit goes away. Faces
  stay well-shaped (fatness `0.44–0.68`), and the certified violations fall to
  `≈ 0.03`. That is small but not zero, so those runs are close to feasible, not
  exactly feasible.
- **The areas have not converged.** The intrinsic optima found (`26.7` for g = 0,
  `41.7` for g = 1) are far above `2π`. They are limited by the evaluation budget,
  not by geometry. COBYLA needs `n + 1` evaluations just to build its starting
  simplex, and with 59 / 95 / 167 free edges, `maxiter=80` leaves almost no
  budget for real optimization steps. For g = 1 and g = 2, SciPy raised the
  budget to the minimum of `n + 2` evaluations, so those runs are close to their
  random starting points. No genus-2 run reached feasibility.
- So this run does **not** show the areas converging toward `2π`. It is a
  working, fast pipeline: valid meshes, an exact Heron objective, and a certified
  intrinsic constraint. Getting closer to `2π` would take a larger budget,
  gradient-based solvers, and finer meshes. Theory gives the lower bound for
  genus 0 (Pu/Ivanov) and genus 1 (Bangert–Croke–Ivanov–Katz).

```bash
.venv/bin/python3 scripts/explore_genus2.py            # ≈ 8 s, writes benchmarks/genus_search.json
.venv/bin/python3 scripts/explore_genus2.py --maxiter 2000 --restarts 4 --n-boundary 12
```

---

## Reproducing

```bash
# Toolchain: leanprover/lean4:v4.36.0 (via elan), Mathlib v4.36.0
lake exe cache get          # fetch prebuilt Mathlib oleans
lake build                  # build and check the whole library

# Verify a single module and append a telemetry record
python3 scripts/verify_and_log.py GromovFillingArea.ZetaBound \
  GromovFillingArea/ZetaBound.lean claude-app

# Regenerate the benchmark table
python3 scripts/generate_report.py
```

## Repository Layout

```
GromovFillingArea/
  Basic.lean           # Circle2Pi, IsometricFilling, conjecture statement
  Kuratowski.lean      # distance-profile map + Lipschitz lemmas
  FourierBound.lean    # 2π-periodic lift to ℝ
  ZetaBound.lean       # antipodal triangle bound, ζ(3) odd-harmonic identity
  FourierEnergy.lean   # 14ζ(3)/π positivity, antipodal max bound
  Witness.lean         # identity isometry witness, diameter ≤ π on Circle2Pi
  AntipodalRadius.lean # dist θ (θ + π) = π, sharp π/2 radius bound
  L2Energy.lean        # π²/2 squared antipodal bound, continuity of the lift
  IntegralBound.lean   # π³/2 ≤ ∫₀^{2π} f² (global L² energy bound)
  ParsevalEnergy.lean  # L² membership + Parseval identity for the profile
GromovFillingArea.lean # root module re-exporting all verified modules
CLAUDE.md              # agent protocol (compiler-in-the-loop rules)
scripts/
  verify_and_log.py    # lake-build oracle + JSONL telemetry
  generate_report.py   # benchmark table generator
  explore_genus2.py    # genus 0–2 discrete filling-area search (numerical)
benchmarks/results.jsonl
benchmarks/genus_search.json
.github/workflows/lean_action_ci.yml
```

## Roadmap

- Replace the abstract orientability `Prop` with a genuine 2-manifold structure.
- Fourier-coefficient decay for 1-Lipschitz periodic functions, and the Wirtinger
  energy inequality.
- Combine these into a formal (non-sharp) universal area lower bound.
- Extend the telemetry with token counts and attempt-level diffs, so that
  different prover models can be compared on the same harness.

## License

Apache 2.0. See file headers.

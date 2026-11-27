# Gromov's Filling Area Conjecture — A Neuro-Symbolic Lean 4 Formalization

[![Lean CI](https://github.com/MonodeepMukherjee/gromov_filling_area/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/MonodeepMukherjee/gromov_filling_area/actions/workflows/lean_action_ci.yml)
![Lean](https://img.shields.io/badge/Lean-v4.36.0-blue)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.36.0-blue)
![sorry](https://img.shields.io/badge/sorry-0-brightgreen)
![axioms](https://img.shields.io/badge/custom%20axioms-0-brightgreen)

A machine-checked Lean 4 + Mathlib formalization effort for **Gromov's Filling Area
Conjecture**. An LLM agent writes the proofs, and the Lean kernel checks every step
before anything is accepted.

## Main Result: an end-to-end `4/π` filling area bound

```lean
theorem gromov_universal_four_div_pi_bound (F : IsometricFilling M)
    (h_no_retract : ¬ ∃ r : M → Circle2Pi, Continuous r ∧ ∀ θ : Circle2Pi, r (F.ι θ) = θ) :
    ENNReal.ofReal (4 / Real.pi) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M)
```

Every isometric filling of the circle of length `2π` whose boundary is not a retract of the
filling has 2-dimensional Hausdorff measure at least `4/π`. This is fully kernel-checked.
`#print axioms gromov_universal_four_div_pi_bound` reports only Lean's standard
`propext`, `Classical.choice` and `Quot.sound`: no `sorry` and no custom axioms. The proof
chains the whole library:

1. **Kuratowski embedding.** `x ↦ dist x (ι ·)` is a 1-Lipschitz map `M → (S¹ →ᵇ ℝ)`.
2. **Fundamental Fourier mode.** `g ↦ ĝ(1)` is 1-Lipschitz into `ℂ`, so `P_1 ∘ K` does not
   increase `μH[2]`.
3. **Boundary circle.** `∂M` maps homeomorphically onto the circle of radius `2/π`. The exact
   radius comes from the Fourier coefficient of the tent-function boundary profile.
4. **Disk covering.** If an interior point of the disk were missed, radial projection would
   give a retraction of `M` onto `∂M`.
5. **Area.** The disk of radius `2/π` has area `4/π ≤ μH[2]`.

**What it does and does not claim:**

- **One remaining assumption.** The theorem assumes the topological *no-retraction* hypothesis
  `h_no_retract`. This holds for genuine fillings, for example disks by Brouwer, but
  `IsometricFilling` does not yet encode it: its surface condition is an abstract `Prop`
  field. Every analytic and metric step, including the former `h_fill` covering hypothesis,
  is discharged.
- **Not the conjecture.** `4/π ≈ 1.27` is well below the conjectured sharp bound `2π ≈ 6.28`.
  `PuSymmetrization` proves the sharp `2π` bound only for rotationally symmetric radial
  profiles `φ ≥ sin`, not for general fillings.
- **Normalization.** Mathlib's `μH[2]` is the unnormalized Hausdorff measure. On Euclidean
  `ℂ` it dominates Lebesgue area, and the proof only uses that inequality.

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

> **Scope.** The conjecture is *stated*, not proved. The strongest result is the
> `4/π` bound above, conditional on no-retraction. Every lemma listed below is fully
> kernel-checked. The surface/orientability condition in `IsometricFilling` is currently
> an abstract `Prop` field. Replacing it with a genuine topological-surface structure,
> which would supply `h_no_retract`, is planned future work.

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
| `GromovFillingArea` | 30 | **PASS (0 sorry)** | 50222.1 ms | 35848.5 ms |
| `GromovFillingArea.Witness` | 1 | **PASS (0 sorry)** | 53272.0 ms | 53272.0 ms |
| `GromovFillingArea.AntipodalRadius` | 1 | **PASS (0 sorry)** | 57994.9 ms | 57994.9 ms |
| `GromovFillingArea.L2Energy` | 1 | **PASS (0 sorry)** | 70202.1 ms | 70202.1 ms |
| `GromovFillingArea.IntegralBound` | 2 | **PASS (0 sorry)** | 70766.6 ms | 85030.9 ms |
| `GromovFillingArea.ParsevalEnergy` | 2 | **PASS (0 sorry)** | 48838.1 ms | 44006.3 ms |
| `GromovFillingArea.SpectralBound` | 2 | **PASS (0 sorry)** | 52679.9 ms | 46020.1 ms |
| `GromovFillingArea.OddHarmonics` | 1 | **PASS (0 sorry)** | 54353.8 ms | 54353.8 ms |
| `GromovFillingArea.FourierShift` | 2 | **PASS (0 sorry)** | 57104.9 ms | 65135.9 ms |
| `GromovFillingArea.OddProjection` | 1 | **PASS (0 sorry)** | 59158.2 ms | 59158.2 ms |
| `GromovFillingArea.OddEnergy` | 1 | **PASS (0 sorry)** | 52077.9 ms | 52077.9 ms |
| `GromovFillingArea.OddLowerBound` | 1 | **PASS (0 sorry)** | 50528.2 ms | 50528.2 ms |
| `GromovFillingArea.FourierDecay` | 1 | **PASS (0 sorry)** | 78654.5 ms | 78654.5 ms |
| `GromovFillingArea.OddDecaySeries` | 1 | **PASS (0 sorry)** | 56318.8 ms | 56318.8 ms |
| `GromovFillingArea.WeightedZetaBound` | 1 | **PASS (0 sorry)** | 67142.0 ms | 67142.0 ms |
| `GromovFillingArea.BoundaryProfile` | 2 | **PASS (0 sorry)** | 42278.0 ms | 36425.2 ms |
| `GromovFillingArea.KuratowskiEmbedding` | 1 | **PASS (0 sorry)** | 51283.4 ms | 51283.4 ms |
| `GromovFillingArea.AreaContraction` | 2 | **PASS (0 sorry)** | 52212.3 ms | 43317.8 ms |
| `GromovFillingArea.FourierProjection` | 2 | **PASS (0 sorry)** | 51692.8 ms | 47897.6 ms |
| `GromovFillingArea.BoundaryCircleImage` | 1 | **PASS (0 sorry)** | 49083.3 ms | 49083.3 ms |
| `GromovFillingArea.BoundaryRadius` | 3 | **PASS (0 sorry)** | 59866.7 ms | 54096.1 ms |
| `GromovFillingArea.FundamentalDiskBound` | 2 | **PASS (0 sorry)** | 44840.6 ms | 44432.9 ms |
| `GromovFillingArea.MultiHarmonicBound` | 1 | **PASS (0 sorry)** | 55323.7 ms | 55323.7 ms |
| `GromovFillingArea.TopologicalFilling` | 2 | **PASS (0 sorry)** | 72747.5 ms | 58553.2 ms |
| `GromovFillingArea.BoundaryWinding` | 1 | **PASS (0 sorry)** | 44192.0 ms | 44192.0 ms |
| `GromovFillingArea.RadialRetraction` | 1 | **PASS (0 sorry)** | 46641.7 ms | 46641.7 ms |
| `GromovFillingArea.DiskCovering` | 2 | **PASS (0 sorry)** | 45772.2 ms | 44145.0 ms |
| `GromovFillingArea.UniversalAreaBound` | 1 | **PASS (0 sorry)** | 48760.0 ms | 48760.0 ms |
| `GromovFillingArea.PuSymmetrization` | 2 | **PASS (0 sorry)** | 52798.8 ms | 54669.0 ms |
| `GromovFillingArea.ConformalPuBound` | 1 | **PASS (0 sorry)** | 67604.3 ms | 67604.3 ms |

**Summary:** 34 build targets, 77 logged verification attempts, 34/34 passing. Both
`SpectralBound` attempts passed: the first was rerun after wrapping a 101-character line
to meet the style limit. The second `FourierProjection` run re-verified a `show` → `change`
style-linter fix, and the second `TopologicalFilling` run re-verified its corrected docstrings.
Eleven attempts failed and were repaired from the compiler
diagnostics:

- The first `FourierBound` build failed with a type mismatch.
- The first `IntegralBound` build used the unknown identifier `continuous_add_right`.
  It was fixed by switching to `continuous_id.add continuous_const`.
- The first `ParsevalEnergy` build failed because `haarAddCircle` lives in the
  `AddCircle` namespace. It was fixed by adding `open AddCircle`.
- The first `FourierShift` build failed with "No goals to be solved": `field_simp` had
  already closed the goal. It was fixed by deleting the trailing `ring`.
- The first `BoundaryProfile` build had two errors. A redundant trailing `rfl` gave
  "No goals to be solved", and `AddCircle.norm_coe_eq_abs_iff` was called without its
  explicit period argument `p`. Both were fixed from the diagnostics.
- The first `AreaContraction` build failed to synthesize `MeasurableSpace (Circle2Pi →ᵇ ℝ)`,
  because Mathlib has no measurable structure on bounded continuous functions. It was fixed
  by adding the Borel `σ`-algebra (`borel _`) and its `BorelSpace` instance.
- The first two `BoundaryRadius` builds failed:
  - The FTC lemma needed its antiderivative given explicitly.
  - Two `simp only` calls made no progress.
  - The final complex identity reduced to `4 + I² · 4 = 0`, closed with
    `linear_combination 4 * hI`.
  - `field_simp` / `norm_cast` already closed goals, so trailing `ring` / `omega` were removed.
  - `-4 = -2 ^ 2` needed a final `norm_num`.
- The first `FundamentalDiskBound` build was missing the import
  `Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls`, which provides
  `Complex.volume_closedBall`.
- The first `DiskCovering` build failed because a `rw` inside `Subtype.ext` tried to rewrite
  under the subtype's proof term ("motive is not type correct"). It was fixed by first stating
  the value-level goal with `change`.
- The first `PuSymmetrization` build passed `Real.continuous_sin.intervalIntegrable` without
  its endpoint arguments. It was fixed by applying it to `_ _`.

The root `GromovFillingArea` target was re-verified each time a new module was
exported. Compile times include the `lake build` of each module's dependency chain on a
local machine. `Basic` is checked as a dependency of every target.

---

## Verified Declarations Index

All 116 theorems below are kernel-checked, with no `sorry`, no `admit`, and no
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

### `GromovFillingArea.SpectralBound` — spectral Fourier energy lower bound

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `kuratowskiComplex_norm_sq` | theorem | `‖kuratowskiComplex F x θ‖² = (f_x θ)²` (helper) |
| `kuratowski_haar_integral_eq` | theorem | `∫ ‖kuratowskiComplex F x θ‖² ∂haarAddCircle = (2π)⁻¹ ∫₀^{2π} f(t)² dt` (helper) |
| `kuratowski_haar_l2_lower_bound` | theorem | `π² / 4 ≤ ∫ ‖kuratowskiComplex F x θ‖² ∂haarAddCircle` |
| `kuratowski_fourier_energy_lower_bound` | theorem | `π² / 4 ≤ ∑' n : ℤ, ‖f̂ n‖²` |

### `GromovFillingArea.OddHarmonics` — antipodal difference profile

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `antipodalDiff` | `def` | `Δ_x(θ) = f_x(θ) − f_x(θ + π)` in `ℂ` |
| `circle2Pi_add_pi_add_pi` | theorem | `θ + π + π = θ` on `Circle2Pi` |
| `antipodalDiff_add_pi` | theorem | `Δ_x(θ + π) = −Δ_x(θ)` (odd under the half-period shift) |

### `GromovFillingArea.FourierShift` — half-period shift & even-mode vanishing

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `fourier_add_arg` | theorem | `e_n(a + b) = e_n(a) · e_n(b)` on `Circle2Pi` (helper) |
| `fourier_neg_index_neg_pi` | theorem | `e_{−n}(−π) = (−1)ⁿ` (helper, via `Complex.exp_pi_mul_I`) |
| `fourierCoeff_neg_fun` | theorem | `ĝ_{−}(n) = −ĝ(n)` for `θ ↦ −g θ` (helper) |
| `fourierCoeff_add_pi` | theorem | Fourier coefficients of `θ ↦ g(θ + π)` are `(−1)ⁿ · ĝ(n)` |
| `antipodalDiff_fourierCoeff_even` | theorem | `Δ̂_x(2k) = 0` for every `k : ℤ` (only odd harmonics survive) |

### `GromovFillingArea.OddProjection` — odd-harmonic doubling & Parseval for `Δ_x`

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `fourier_smul_integrable` | theorem | `t ↦ e_n(t) • g(t)` is Haar-integrable for continuous `g` (helper) |
| `fourierCoeff_sub_of_continuous` | theorem | Fourier coefficients of `f − g` are `f̂(n) − ĝ(n)` for continuous `f`, `g` (helper) |
| `kuratowskiComplex_shift_continuous` | theorem | `θ ↦ kuratowskiComplex F x (θ + π)` is continuous (helper) |
| `antipodalDiff_continuous` | theorem | `Continuous (antipodalDiff F x)` (helper) |
| `antipodalDiff_memLp` | theorem | `MemLp (antipodalDiff F x) 2 haarAddCircle` (helper) |
| `antipodalDiff_fourierCoeff_odd` | theorem | `Δ̂_x(2k + 1) = 2 · f̂_x(2k + 1)` |
| `antipodalDiff_parseval_hasSum` | theorem | `HasSum (n ↦ ‖Δ̂_x(n)‖²) (∫ ‖Δ_x θ‖² ∂haarAddCircle)` |

### `GromovFillingArea.OddEnergy` — odd-harmonic spectral energy identity

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `odd_index_injective` | theorem | `k ↦ 2k + 1` is injective on `ℤ` (helper) |
| `antipodalDiff_energy_eq_zero_of_not_odd` | theorem | `‖Δ̂_x(n)‖² = 0` when `n` is not odd (helper) |
| `kuratowski_odd_fourier_summable` | theorem | `Summable (k ↦ ‖f̂_x(2k + 1)‖²)` |
| `kuratowski_odd_fourier_energy_eq` | theorem | `4 · ∑' k, ‖f̂_x(2k + 1)‖² = ∫ ‖Δ_x θ‖² ∂haarAddCircle` |

### `GromovFillingArea.OddLowerBound` — uniform amplitude & odd-coefficient bounds

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `antipodalDiff_norm_le_pi` | theorem | `‖Δ_x(θ)‖ ≤ π` for every `x : M`, `θ` |
| `fourier_apply_norm_le_one` | theorem | `‖e_n(t)‖ ≤ 1` on `Circle2Pi` (helper) |
| `antipodalDiff_fourierCoeff_norm_le` | theorem | `‖Δ̂_x(n)‖ ≤ π` for every `n : ℤ` (helper) |
| `kuratowski_odd_fourierCoeff_norm_le` | theorem | `‖f̂_x(2k + 1)‖ ≤ π / 2` for every `k : ℤ` |

### `GromovFillingArea.FourierDecay` — `O(1/|n|)` Fourier decay for Lipschitz profiles

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `fourierCoeff_add_shift` | theorem | Fourier coefficients of `θ ↦ g(θ + s)` are `e_{−n}(−s) · ĝ(n)` (helper) |
| `fourier_neg_index_neg_pi_div` | theorem | `e_{−n}(−π/n) = −1` for `n ≠ 0` (helper) |
| `fourierCoeff_norm_le_of_norm_le` | theorem | `‖g θ‖ ≤ C` for all `θ` implies `‖ĝ(n)‖ ≤ C` (helper) |
| `two_mul_fourierCoeff_eq_sub_shift` | theorem | `2 · ĝ(n)` equals the `n`-th coefficient of `θ ↦ g(θ) − g(θ + π/n)` |
| `kuratowskiComplex_shift_diff_norm_le` | theorem | `‖f_x(θ) − f_x(θ + π/n)‖ ≤ π/\|n\|` (helper) |
| `kuratowski_fourierCoeff_decay` | theorem | `‖f̂_x(n)‖ ≤ π / (2\|n\|)` for every `n ≠ 0` |

### `GromovFillingArea.OddDecaySeries` — odd-harmonic inverse-cube bound

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `kuratowski_odd_fourierCoeff_decay` | theorem | `‖f̂_x(2k + 1)‖ ≤ π / (2 · \|2k + 1\|)` for every `k : ℤ` |
| `kuratowski_pos_odd_weighted_bound` | theorem | `‖f̂_x(2k + 1)‖² / (2k + 1) ≤ (π² / 4) · 1 / (2k + 1)³` for every `k : ℕ` |

### `GromovFillingArea.WeightedZetaBound` — closed-form weighted ζ(3) bound

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `odd_nat_index_injective` | theorem | `k ↦ 2k + 1` is injective on `ℕ` (helper) |
| `summable_odd_inv_cube` | theorem | `Summable (k ↦ 1 / (2k + 1)³)` over `ℕ` (helper) |
| `kuratowski_pos_odd_weighted_nonneg` | theorem | `0 ≤ ‖f̂_x(2k + 1)‖² / (2k + 1)` (helper) |
| `kuratowski_pos_odd_weighted_summable` | theorem | `Summable (k ↦ ‖f̂_x(2k + 1)‖² / (2k + 1))` over `ℕ` |
| `kuratowski_weighted_odd_series_le` | theorem | `∑' k : ℕ, ‖f̂_x(2k + 1)‖² / (2k + 1) ≤ (7π² / 32) · ζ(3)` |

### `GromovFillingArea.BoundaryProfile` — boundary profile & tight antipodal equality

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `kuratowskiMap_boundary` | theorem | `f_{ι θ₀}(θ) = dist θ₀ θ` at boundary points |
| `circle2Pi_exists_rep_Ioc` | theorem | every `y : Circle2Pi` has a representative `t ∈ (−π, π]` (helper) |
| `circle2Pi_norm_coe_of_abs_le` | theorem | `‖(s : Circle2Pi)‖ = \|s\|` when `\|s\| ≤ π` (helper) |
| `circle2Pi_norm_add_norm_sub_pi` | theorem | `‖y‖ + ‖y − π‖ = π` on `Circle2Pi` (helper) |
| `circle2Pi_dist_add_antipodal` | theorem | `dist θ₀ θ + dist θ₀ (θ + π) = π`, so the antipodal bound is an equality on `∂M` |

### `GromovFillingArea.KuratowskiEmbedding` — Banach-space embedding `M → (Circle2Pi →ᵇ ℝ)`

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `kuratowskiBanach` | `def` | `x ↦ (θ ↦ dist x (ι θ))` as a bounded continuous function (sup norm) |
| `kuratowskiBanach_apply` | theorem | `kuratowskiBanach F x θ = f_x(θ)` (helper, `rfl`) |
| `kuratowskiBanach_lipschitzWith` | theorem | `LipschitzWith 1 (kuratowskiBanach F)` |
| `kuratowskiBanach_boundary_isometry` | theorem | `dist (K(ι θ₁)) (K(ι θ₂)) = dist θ₁ θ₂`, so the embedding is isometric on `∂M` |

### `GromovFillingArea.AreaContraction` — 2-dimensional Hausdorff area contraction

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `BoundedContinuousFunction.circle2PiMeasurableSpace` | `instance` | Borel `σ`-algebra on `Circle2Pi →ᵇ ℝ` |
| `BoundedContinuousFunction.circle2PiBorelSpace` | `instance` | `BorelSpace (Circle2Pi →ᵇ ℝ)` |
| `lipschitzWith_one_hausdorffMeasure_range_le` | theorem | `LipschitzWith 1 f → μH[2] (range f) ≤ μH[2] univ` (helper) |
| `kuratowskiBanach_hausdorffMeasure_le` | theorem | `μH[2] (range (kuratowskiBanach F)) ≤ μH[2] (univ : Set M)` |
| `kuratowskiBanach_proj_hausdorffMeasure_le` | theorem | for any 1-Lipschitz map `π` out of `S¹ →ᵇ ℝ`, `μH[2] (range (π ∘ K)) ≤ μH[2] (univ : Set M)` |

### `GromovFillingArea.FourierProjection` — 1-Lipschitz Fourier mode projections

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `fourierProj` | `def` | `g ↦ ĝ(n)`, the `n`-th Fourier coefficient as a map `(S¹ →ᵇ ℝ) → ℂ` |
| `bcf_complex_continuous` | theorem | `θ ↦ (g θ : ℂ)` is continuous (helper) |
| `fourierProj_lipschitzWith` | theorem | `LipschitzWith 1 (fourierProj n)` for every `n : ℤ` |
| `kuratowski_fourierProj_hausdorffMeasure_le` | theorem | `μH[2] {f̂_x(n) : x ∈ M} ≤ μH[2] (univ : Set M)` in `ℂ` |

### `GromovFillingArea.BoundaryCircleImage` — rotational equivariance & circular boundary image

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `kuratowskiMap_boundary_shift` | theorem | `f_{ι θ₀}(θ) = f_{ι 0}(θ − θ₀)` (helper) |
| `fourier_norm_apply` | theorem | `‖e_n(θ)‖ = 1` (helper) |
| `fourierProj_boundary_eq` | theorem | `P_n(K(ι θ₀)) = e_{−n}(θ₀) · P_n(K(ι 0))` (rotation equivariance) |
| `fourierProj_boundary_norm` | theorem | `‖P_n(K(ι θ₀))‖ = ‖P_n(K(ι 0))‖`, so `∂M` maps onto a circle in `ℂ` |

### `GromovFillingArea.BoundaryRadius` — exact boundary circle radii for odd modes

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `kuratowskiMap_boundary_zero_eq_min` | theorem | `f_{ι 0}(t) = min t (2π − t)` for `t ∈ [0, 2π]` (tent function) |
| `fourier_neg_coe_eq_cexp` | theorem | `e_{−n}(x) = exp(−n · I · x)` for real `x` (helper) |
| `integral_cexp_mul_affine` | theorem | `∫_u^v exp(cx)(p + qx) dx` in closed form for `c ≠ 0` (helper, FTC) |
| `cexp_odd_mul_pi` | theorem | `exp(−(2k + 1) · I · π) = −1` (helper) |
| `cexp_int_mul_two_pi` | theorem | `exp(−n · I · 2π) = 1` (helper) |
| `boundary_integrand_continuous` | theorem | the real-variable coefficient integrand is continuous (helper) |
| `boundary_odd_integral` | theorem | `∫₀^{2π} e_{−n}(x) · f_{ι 0}(x) dx = −4 / n²` for `n = 2k + 1` (helper) |
| `fourierProj_boundary_odd_norm` | theorem | `‖P_{2k+1}(K(ι 0))‖ = 2 / ((2k + 1)² π)` |

### `GromovFillingArea.FundamentalDiskBound` — fundamental-mode filling lower bound `4/π`

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `complex_measurableEquivPi_lipschitz` | theorem | `z ↦ ![re z, im z]` is 1-Lipschitz from Euclidean `ℂ` to sup-metric `Fin 2 → ℝ` (helper) |
| `volume_le_hausdorffMeasure_two_complex` | theorem | `volume s ≤ μH[2] s` for every `s ⊆ ℂ` (helper) |
| `volume_fundamental_disk` | theorem | `volume (closedBall 0 (2/π)) = 4/π` in `ℂ` (helper) |
| `hausdorffMeasure_two_fundamental_disk` | theorem | `4/π ≤ μH[2] (closedBall 0 (2/π))` in `ℂ` |
| `fundamental_mode_filling_area_bound` | theorem | if `closedBall 0 (2/π) ⊆ range (P_1 ∘ K)`, then `4/π ≤ μH[2] (univ : Set M)` |

> **Normalization note.** Mathlib's `μH[d]` is the *unnormalized* Hausdorff measure. It equals
> Lebesgue measure on the sup-metric space `Fin n → ℝ` (`hausdorffMeasure_pi_real`), but not on
> Euclidean `ℂ`. There, classically, `μH[2] = (4/π) · volume`, and Mathlib leaves this factor as
> a TODO. So `hausdorffMeasure_two_fundamental_disk` is stated and proved as the true lower bound
> `4/π ≤ μH[2] (closedBall 0 (2/π))`, rather than an equality, which would be false: the
> classical value is `16/π²`. This bound is all that `fundamental_mode_filling_area_bound` needs.

### `GromovFillingArea.MultiHarmonicBound` — general odd-harmonic filling bounds

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `volume_odd_disk` | theorem | `volume (closedBall 0 (2/((2k+1)² π))) = 4/((2k+1)⁴ π)` in `ℂ` (helper) |
| `hausdorffMeasure_two_odd_disk` | theorem | `4/((2k+1)⁴ π) ≤ μH[2] (closedBall 0 (2/((2k+1)² π)))` |
| `odd_harmonic_filling_area_bound` | theorem | if `closedBall 0 R_{2k+1} ⊆ range (P_{2k+1} ∘ K)`, then `4/((2k+1)⁴ π) ≤ μH[2] (univ : Set M)` |

### `GromovFillingArea.TopologicalFilling` — boundary circle for the fundamental mode

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `norm_inv_mul_eq_one` | theorem | `‖z‖ = R > 0 → ‖R⁻¹ · z‖ = 1` (radial rescaling onto the unit circle) |
| `fourierProj_one_boundary_mem_sphere` | theorem | `P_1(K(ι θ₀)) ∈ sphere 0 (2/π)` for every boundary angle `θ₀` |

### `GromovFillingArea.BoundaryWinding` — bijectivity of the fundamental boundary map

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `fourierProj_one_base_ne_zero` | theorem | `P_1(K(ι 0)) ≠ 0` (its norm is `2/π`) (helper) |
| `fourierProj_one_boundary_injective` | theorem | `θ₀ ↦ P_1(K(ι θ₀))` is injective on `Circle2Pi` |
| `fourierProj_one_boundary_surjective` | theorem | every `w ∈ sphere 0 (2/π)` equals `P_1(K(ι θ₀))` for some `θ₀` |

> **Status.** `∂M` maps bijectively onto the circle of radius `2/π` under `P_1 ∘ K`. The
> covering step is formalized in `DiskCovering` below, conditional on a no-retraction hypothesis.

### `GromovFillingArea.RadialRetraction` — closed-form radial projection onto `sphere 0 R`

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `radialRayParam` | `def` | positive root `t = (−b + √(b² − ac))/a` of `‖p + t(z − p)‖² = R²` |
| `radialProj` | `def` | `z ↦ p + t(z − p)`, the radial projection from `p` onto `sphere 0 R` |
| `normSq_add_ofReal_mul` | theorem | `‖p + t d‖² = ‖p‖² + 2t Re(p d̄) + t²‖d‖²` (helper) |
| `quadratic_pos_root` | theorem | the positive root solves `a t² + 2bt + c = 0` when `a > 0`, `b² − ac ≥ 0` (helper) |
| `quadratic_pos_root_eq_one` | theorem | if `c + 2b + a = 0`, `a > 0`, `c < 0`, the positive root is `1` (helper) |
| `radialProj_mem_sphere` | theorem | `‖p‖ < R`, `z ≠ p` ⇒ `radialProj p R z ∈ sphere 0 R` |
| `radialProj_eq_self_of_mem_sphere` | theorem | `‖p‖ < R`, `z ∈ sphere 0 R` ⇒ `radialProj p R z = z` |

### `GromovFillingArea.DiskCovering` — topological disk covering via no-retraction

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `radialProj_continuousOn` | theorem | `ContinuousOn (radialProj p R) {z \| z ≠ p}` |
| `disk_covered_of_no_retraction` | theorem | if `f : M → ℂ` is continuous, `f ∘ ι` is a homeomorphism `Circle2Pi ≃ₜ sphere 0 R`, and `M` has no continuous retraction onto `ι`, then `closedBall 0 R ⊆ range f` |

> **Status of `h_fill`.** Discharged in `UniversalAreaBound`. The boundary homeomorphism is
> `fourierProjOneBoundaryHomeomorph`, and the only remaining input is the no-retraction hypothesis.

### `GromovFillingArea.UniversalAreaBound` — end-to-end `4/π` area bound

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `fourierProjOneBoundaryHomeomorph` | `def` | `θ₀ ↦ P_1(K(ι θ₀))` as a homeomorphism `Circle2Pi ≃ₜ sphere 0 (2/π)` (compact → T2) |
| `gromov_universal_four_div_pi_bound` | theorem | **main result:** no retraction of `M` onto `ι` ⇒ `4/π ≤ μH[2] (univ : Set M)` |

### `GromovFillingArea.PuSymmetrization` — Pu's sharp `2π` bound for symmetric profiles

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `hemisphere_radial_area` | theorem | `2π · ∫₀^{π/2} sin t dt = 2π` (area of the round hemisphere) |
| `pu_symmetric_filling_area_ge_two_pi` | theorem | continuous `φ` with `sin t ≤ φ t` on `[0, π/2]` ⇒ `2π ≤ 2π · ∫₀^{π/2} φ` |

This is the analytic core of Pu's theorem (genus 0) for a rotationally symmetric disk
`dr² + φ(r)² dθ²`. It is stated about the radial profile `φ` directly: the link from an
`IsometricFilling` to such a profile is not formalized.

### `GromovFillingArea.ConformalPuBound` — angular averaging never increases conformal area

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `angularMean` | `def` | `angularMean f = (2π)⁻¹ · ∫₀^{2π} f θ dθ` |
| `angularMean_sq_le` | theorem | continuous `f` ⇒ `(angularMean f)² ≤ angularMean (f²)` (via the variance `∫ (f − c)² ≥ 0`) |
| `radial_symmetrized_area_le` | theorem | `w ≥ 0` on `[0, 1]` ⇒ `∫₀¹ w r · (angularMean (λ r))² ≤ ∫₀¹ w r · angularMean ((λ r)²)` |

This is the angular-averaging step of Pu's symmetrization for conformal metrics
`λ(r, θ)² (dr² + r² dθ²)`. It is stated for a fixed weight `w` and factor `λ`: it does not
yet show that the averaged metric is still an isometric filling.

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
  SpectralBound.lean   # π²/4 ≤ Haar L² energy = ∑ ‖f̂ n‖²
  OddHarmonics.lean    # antipodal difference Δ_x, odd under θ ↦ θ + π
  FourierShift.lean    # π-shift ↦ (−1)ⁿ on coefficients; even modes of Δ_x vanish
  OddProjection.lean   # Δ̂_x(2k+1) = 2 f̂_x(2k+1); Parseval for Δ_x
  OddEnergy.lean       # 4 ∑ ‖f̂_x(2k+1)‖² = ‖Δ_x‖²_{L²(haar)}
  OddLowerBound.lean   # ‖Δ_x‖ ≤ π pointwise; ‖f̂_x(2k+1)‖ ≤ π/2
  FourierDecay.lean    # ‖f̂_x(n)‖ ≤ π/(2|n|) via the π/n half-wavelength shift
  OddDecaySeries.lean  # odd-mode decay and ‖f̂_x(2k+1)‖²/(2k+1) ≤ (π²/4)/(2k+1)³
  WeightedZetaBound.lean # ∑ ‖f̂_x(2k+1)‖²/(2k+1) ≤ (7π²/32) ζ(3)
  BoundaryProfile.lean # f_{ι θ₀}(θ) = dist θ₀ θ; antipodal sum = π on ∂M
  KuratowskiEmbedding.lean # 1-Lipschitz M → (S¹ →ᵇ ℝ), isometric on ∂M
  AreaContraction.lean # μH[2] contraction under K and 1-Lipschitz projections
  FourierProjection.lean # 1-Lipschitz g ↦ ĝ(n); projected area ≤ Area(M)
  BoundaryCircleImage.lean # ∂M ↦ circle of radius ‖P_n(K(ι 0))‖ in ℂ
  BoundaryRadius.lean  # tent profile; odd radius ‖P_{2k+1}‖ = 2/((2k+1)² π)
  FundamentalDiskBound.lean # volume ≤ μH[2] on ℂ; filling the 2/π disk ⇒ Area(M) ≥ 4/π
  MultiHarmonicBound.lean # odd mode 2k+1: filling its disk ⇒ Area(M) ≥ 4/((2k+1)⁴ π)
  TopologicalFilling.lean # ∂M ↦ sphere 0 (2/π) under P_1 ∘ K; radial rescaling
  BoundaryWinding.lean # θ₀ ↦ P_1(K(ι θ₀)) is a bijection Circle2Pi → sphere 0 (2/π)
  RadialRetraction.lean # explicit radial projection ℂ ∖ {p} → sphere 0 R, fixing the sphere
  DiskCovering.lean    # radialProj continuous off p; no retraction ⇒ closedBall 0 R ⊆ range f
  UniversalAreaBound.lean # main theorem: no retraction ⇒ Area(M) ≥ 4/π
  PuSymmetrization.lean # hemisphere area 2π; sin ≤ φ on [0, π/2] ⇒ 2π ∫ φ ≥ 2π
  ConformalPuBound.lean # (mean λ)² ≤ mean λ²; angular averaging never increases area
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

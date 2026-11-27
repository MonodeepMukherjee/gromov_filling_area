# Gromov's Filling Area Conjecture — A Neuro-Symbolic Lean 4 Formalization

[![Lean CI](https://github.com/MonodeepMukherjee/gromov_filling_area/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/MonodeepMukherjee/gromov_filling_area/actions/workflows/lean_action_ci.yml)
![Lean](https://img.shields.io/badge/Lean-v4.36.0-blue)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.36.0-blue)
![sorry](https://img.shields.io/badge/sorry-0-brightgreen)
![axioms](https://img.shields.io/badge/custom%20axioms-0-brightgreen)

A machine-checked Lean 4 + Mathlib formalization effort for **Gromov's Filling Area
Conjecture**. An LLM agent writes the proofs, and the Lean kernel checks every step
before anything is accepted.

## Main Result: an end-to-end `π²/2` filling area bound

```lean
theorem gromov_universal_pi_sq_div_two_bound (F : IsometricFilling M) :
    ENNReal.ofReal (Real.pi ^ 2 / 2) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M)
```

Every isometric filling of the circle of length `2π` has 2-dimensional Hausdorff measure at
least `π²/2 ≈ 4.9348`, which is `0.785 · 2π`. `IsometricFilling` includes the field
`no_boundary_retraction`, which says the boundary is not a retract of the filling. This is
fully kernel-checked. `#print axioms gromov_universal_pi_sq_div_two_bound` reports only
Lean's standard `propext`, `Classical.choice` and `Quot.sound`: no `sorry` and no custom
axioms. It supersedes `gromov_universal_pi_bound` (`π ≈ 3.14`, `SharpFirstMode`) and
`gromov_universal_four_div_pi_bound` (`4/π ≈ 1.27`, `UniversalAreaBound`), which are kept.
The proof uses only two boundary points, `0` and `π/2`:

1. **Quarter-circle pair map.** `q(x) = (d(x, ι 0), d(x, ι (π/2)))` is 1-Lipschitz into the
   **sup-norm** plane `Fin 2 → ℝ` (`quarterPairMap_lipschitzWith`). There Mathlib's `μH[2]`
   is exactly Lebesgue area (`hausdorffMeasure_pi_real`), so `μH[2](q(M)) ≤ μH[2](M)`.
2. **Boundary diamond.** `q ∘ ι` maps the circle injectively onto the boundary of the `L¹`
   diamond `|u − π/2| + |v − π/2| ≤ π/2` (`quarterCircle_boundary_diamond`,
   `quarterPairMap_boundary_injective`). Surjectivity uses an explicit angle in each
   quadrant (`exists_boundary_angle`).
3. **Diamond covering.** The radial gauge map `diamondToComplex` sends the diamond to the
   disk of radius `π/2` and its boundary to the circle. It is continuous and injective,
   with an explicit left inverse. So `q ∘ ι` becomes a homeomorphism onto the circle, and
   `disk_covered_of_no_retraction` shows `q(M)` contains the whole diamond
   (`quarterDiamond_subset_range`).
4. **Area.** The diamond is the preimage of a square under a shear of determinant `−2`, so
   `μH[2](diamond) = π²/2` (`hausdorffMeasure_two_quarterDiamond`). Chaining:
   `π²/2 = μH[2](diamond) ≤ μH[2](q(M)) ≤ μH[2](M)`.

This pair was found numerically by `scripts/conjecture_discovery.py` (see Neuro-Symbolic
Invariant Discovery), which ranked it as the best single boundary-pair calibration. It was
then formalized in four modules: `QuarterCircleSquare`, `DiamondGeometry`,
`DiamondAreaBound` and, for the earlier `π` bound, `SharpFirstMode`.

**What it does and does not claim:**

- **One remaining assumption, now a structure field.** The topological *no-retraction*
  condition is the field `IsometricFilling.no_boundary_retraction`, so the theorem takes no
  extra hypotheses. This moves the assumption into the definition but does not derive it. It
  holds for genuine compact surfaces with one boundary circle, for example disks by Brouwer,
  but the surface condition is still an abstract `Prop` field, so it is not proved from
  surface topology. The field also rules out degenerate "fillings" such as `M = Circle2Pi`
  with `ι = id`, which retracts onto itself. Every analytic and metric step, including the
  former `h_fill` covering hypothesis, is discharged.
- **Not the conjecture.** `π²/2 ≈ 4.93` is below the conjectured sharp bound `2π ≈ 6.28`.
  `PuSymmetrization` proves the sharp `2π` bound only for rotationally symmetric radial
  profiles `φ ≥ sin`, not for general fillings.
- **Normalization.** Mathlib's `μH[2]` is the unnormalized Hausdorff measure. On Euclidean
  `ℂ` it dominates Lebesgue area. On the sup-norm plane `Fin 2 → ℝ` it *equals* Lebesgue
  area, which is why the `π²/2` proof maps into that plane rather than `ℂ`.

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
> `π²/2` bound above, using the no-retraction field of `IsometricFilling`. Every lemma listed
> below is fully kernel-checked. The surface/orientability condition in `IsometricFilling` is
> currently an abstract `Prop` field. Replacing it with a genuine topological-surface
> structure, from which `no_boundary_retraction` would be proved, is planned future work.

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
| `GromovFillingArea` | 40 | **PASS (0 sorry)** | 51944.3 ms | 35848.5 ms |
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
| `GromovFillingArea.UniversalAreaBound` | 2 | **PASS (0 sorry)** | 95603.4 ms | 48760.0 ms |
| `GromovFillingArea.PuSymmetrization` | 2 | **PASS (0 sorry)** | 52798.8 ms | 54669.0 ms |
| `GromovFillingArea.ConformalPuBound` | 2 | **PASS (0 sorry)** | 59369.4 ms | 51134.4 ms |
| `GromovFillingArea.RadialGeodesicBound` | 1 | **PASS (0 sorry)** | 54800.6 ms | 54800.6 ms |
| `GromovFillingArea.ConformalDiskArea` | 3 | **PASS (0 sorry)** | 58721.2 ms | 70388.8 ms |
| `GromovFillingArea.HemisphereCalibration` | 1 | **PASS (0 sorry)** | 46988.3 ms | 46988.3 ms |
| `GromovFillingArea.WeightedRadialBound` | 1 | **PASS (0 sorry)** | 51776.9 ms | 51776.9 ms |
| `GromovFillingArea.ConformalBoundaryLength` | 2 | **PASS (0 sorry)** | 54945.2 ms | 50490.8 ms |
| `GromovFillingArea.Basic` | 1 | **PASS (0 sorry)** | 59410.7 ms | 59410.7 ms |
| `GromovFillingArea.SharpFirstMode` | 3 | **PASS (0 sorry)** | 48416.0 ms | 55791.1 ms |
| `GromovFillingArea.QuarterCircleSquare` | 2 | **PASS (0 sorry)** | 51260.6 ms | 45284.5 ms |
| `GromovFillingArea.DiamondGeometry` | 2 | **PASS (0 sorry)** | 56146.4 ms | 53947.8 ms |
| `GromovFillingArea.DiamondAreaBound` | 1 | **PASS (0 sorry)** | 53493.2 ms | 53493.2 ms |

**Summary:** 44 build targets, 106 logged verification attempts, 44/44 passing. Both
`SpectralBound` attempts passed: the first was rerun after wrapping a 101-character line
to meet the style limit. The second `FourierProjection` run re-verified a `show` → `change`
style-linter fix, and the second `TopologicalFilling` run re-verified its corrected docstrings.
The second `ConformalPuBound` run re-verified a `show` → `change` style-linter fix.
Eighteen attempts failed and were repaired from the compiler
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
- The first two `ConformalDiskArea` builds failed in the FTC derivative step. After `convert`,
  the goal was stated with `id ^ 2` instead of mentioning `hemisphereConformalFactor`, so
  `simp only` and `rw` on the definition made no progress. It was fixed by splitting the
  function and derivative goals and unfolding `id` and `Pi.pow_apply`.
- The first `ConformalBoundaryLength` build failed with a type mismatch: rewriting
  `2 * π` to `2 * π * 1` with `conv_lhs` also rewrote the `2 * π` inside
  `conformalBoundaryLength`. It was fixed by instantiating `mul_le_mul_iff_of_pos_left`
  at `1` and `angularMean (lam 1)` and simplifying `mul_one`.
- The first two `SharpFirstMode` builds failed:
  - a `simp only` made no progress;
  - `NNReal.coe_mk` did not match the anonymous-constructor coercion `↑⟨2 / π, _⟩`, and
    neither did a `mul_one` rewrite in `ℝ≥0`; these were fixed by naming the constant
    `K` and using `change` / `rfl` / `LipschitzWith.weaken`;
  - `conv_rhs => rw [← norm_mul_exp_arg_mul_I w]` also rewrote the `w` inside `arg w`;
    a `calc` that rewrites only the outer occurrence fixed it.
- The first `QuarterCircleSquare` build used `le_or_lt`, which this Mathlib has renamed
  to `le_or_gt`.
- The first `DiamondGeometry` build had three errors: `hausdorffMeasure_pi_real` was given a
  wrong `MeasureTheory.Measure.` prefix, `positivity` could not show `0 ≤ π/2 − (−π/2)`
  (fixed with `linarith`), and the deprecated `Set.mem_setOf_eq` was replaced by
  `Set.mem_ofPred_eq`.

The root `GromovFillingArea` target was re-verified each time a new module was
exported. Compile times include the `lake build` of each module's dependency chain on a
local machine. `Basic` is checked as a dependency of every target and was also verified
directly after `no_boundary_retraction` was added.

---

## Verified Declarations Index

All 163 theorems below are kernel-checked, with no `sorry`, no `admit`, and no
custom `axiom`.

### `GromovFillingArea.Basic` — problem statement

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `Circle2Pi` | `abbrev` | `AddCircle (2 * π)`, the Riemannian circle of length `2π` |
| `IsometricFilling` | `structure` | Compact metric `M` with an isometric embedding `ι : Circle2Pi → M` and no continuous retraction `M → Circle2Pi` onto `ι` (`no_boundary_retraction`) |
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
> covering step is formalized in `DiskCovering` below, using the no-retraction condition.

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
> `fourierProjOneBoundaryHomeomorph`, and the no-retraction input is `F.no_boundary_retraction`.

### `GromovFillingArea.UniversalAreaBound` — end-to-end `4/π` area bound

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `fourierProjOneBoundaryHomeomorph` | `def` | `θ₀ ↦ P_1(K(ι θ₀))` as a homeomorphism `Circle2Pi ≃ₜ sphere 0 (2/π)` (compact → T2) |
| `gromov_universal_four_div_pi_bound` | theorem | (superseded by `gromov_universal_pi_bound`) every `F : IsometricFilling M` has `4/π ≤ μH[2] (univ : Set M)`, via `F.no_boundary_retraction` |

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

### `GromovFillingArea.RadialGeodesicBound` — antipodal diameter ⇒ symmetrized radius `≥ π/2`

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `radialRayLength` | `def` | `radialRayLength λ θ = ∫₀¹ λ(r, θ) dr` |
| `angularMean_ge_half_pi_of_antipodal_sum` | theorem | continuous `2π`-periodic `L` with `π ≤ L θ + L (θ + π)` ⇒ `π/2 ≤ angularMean L` |
| `symmetrized_radial_radius_ge_half_pi` | theorem | jointly continuous, `2π`-periodic `λ` with antipodal ray sum `≥ π` ⇒ `π/2 ≤ ∫₀¹ angularMean (λ r) dr` (Fubini swap) |

The antipodal ray-sum condition is taken as a hypothesis. It is not yet derived from the
isometric boundary condition of an `IsometricFilling`.

### `GromovFillingArea.ConformalDiskArea` — stereographic hemisphere calibration

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `hemisphereConformalFactor` | `def` | `λ(r) = 2 / (1 + r²)`, the stereographic factor of the unit hemisphere |
| `hemisphere_conformal_inradius` | theorem | `∫₀¹ λ(r) dr = π/2` (via `2 arctan`) |
| `hemisphere_conformal_area` | theorem | `2π · ∫₀¹ r · λ(r)² dr = 2π` (FTC with antiderivative `−2 / (1 + r²)`) |

These calibrate the model case: the round hemisphere meets the `π/2` radius bound of
`RadialGeodesicBound` exactly and has conformal area `2π`.

### `GromovFillingArea.HemisphereCalibration` — sharp `2π` bound for conformal disks

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `hemisphere_calibration_pointwise` | theorem | `0 ≤ r` ⇒ `r h² + 2 r h (u − h) ≤ r u²` with `h = hemisphereConformalFactor r` |
| `conformal_disk_area_ge_two_pi` | theorem | jointly continuous `λ` with `2/(1+r²) ≤ angularMean (λ r)` on `[0, 1]` ⇒ `2π ≤ 2π · ∫₀¹ r · angularMean (λ(r, ·)²) dr` |

The proof chains the hemisphere area `2π`, the pointwise calibration, and the symmetrization
bound `radial_symmetrized_area_le` with weight `w r = r`. The hypothesis is a pointwise
domination of the averaged factor by the hemisphere profile. It is stronger than the
antipodal radius bound `π/2` of `RadialGeodesicBound` and is not derived from it, so this
is not yet the genus-0 case of the conjecture.

### `GromovFillingArea.WeightedRadialBound` — integrated calibration & moment condition

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `conformal_disk_calibrated_area_bound` | theorem | jointly continuous `λ` ⇒ `2π + 4π · ∫₀¹ r h (angularMean (λ r) − h) dr ≤ 2π · ∫₀¹ r · angularMean (λ(r, ·)²) dr`, with `h = 2/(1+r²)` |
| `conformal_disk_area_ge_two_pi_of_moment` | theorem | if the moment `∫₀¹ r h (angularMean (λ r) − h) dr` is `≥ 0`, the conformal area is `≥ 2π` |

This replaces the pointwise domination hypothesis of `HemisphereCalibration` by one integral
condition. Like that hypothesis, the moment condition is assumed, not derived from the
isometric boundary condition.

### `GromovFillingArea.ConformalBoundaryLength` — boundary circumference & moment domination

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `conformalBoundaryLength` | `def` | `2π · angularMean (λ 1)`, the circumference at `r = 1` |
| `two_pi_le_conformalBoundaryLength_iff` | theorem | `2π ≤ conformalBoundaryLength λ ↔ 1 ≤ angularMean (λ 1)` |
| `conformal_disk_area_ge_two_pi_of_moment_ge` | theorem | if `∫₀¹ r h² dr ≤ ∫₀¹ r h · angularMean (λ r) dr`, the conformal area is `≥ 2π` |

The second theorem restates the moment condition of `WeightedRadialBound` as a comparison of
two integrals. The boundary circumference condition is recorded but not yet used to derive it.

### `GromovFillingArea.SharpFirstMode` — sharp `2/π` Lipschitz constant & `π` area bound

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `integral_abs_cos_add` | theorem | `∫₀^{2π} \|cos (x + φ)\| dx = 4` (periodic shift to `[−π/2, 3π/2]`, split at `π/2`) (helper) |
| `continuous_coe_circle2Pi` | theorem | the coercion `ℝ → Circle2Pi` is continuous (helper) |
| `re_exp_mul_fourierProj_one` | theorem | `Re(e^{iφ} δ̂(1)) = (2π)⁻¹ ∫₀^{2π} cos (x − φ) δ(x) dx` (helper) |
| `re_exp_mul_fourierProj_one_le` | theorem | `Re(e^{iφ} δ̂(1)) ≤ (2/π) ‖δ‖` (helper) |
| `fourierProj_one_sharp_lipschitz` | theorem | `fourierProj 1` is `(2/π)`-Lipschitz |
| `gromov_universal_pi_bound` | theorem | (superseded by `gromov_universal_pi_sq_div_two_bound`) every `F : IsometricFilling M` has `π ≤ μH[2] (univ : Set M)` |

### `GromovFillingArea.QuarterCircleSquare` — quarter-circle pair map & boundary diamond

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `quarterPairMap` | `def` | `x ↦ ![f_x(0), f_x(π/2)] : M → (Fin 2 → ℝ)` (sup-norm plane) |
| `quarterPairMap_lipschitzWith` | theorem | `quarterPairMap F` is 1-Lipschitz into the sup-norm plane |
| `quarterCircle_boundary_diamond` | theorem | for every `θ`, `\|d(0, θ) − π/2\| + \|d(π/2, θ) − π/2\| = π/2`, i.e. `∂M` maps onto the boundary of the `L¹` diamond of area `π²/2` |

The diamond proof picks a representative `t ∈ (−π, π]` and splits at `−π/2`, `0`, `π/2`.
On `(−π, −π/2]` the difference `π/2 − t` is shifted down by the period `2π` before
`circle2Pi_norm_coe_of_abs_le` applies.

> **Status.** These are the first two steps toward `Area ≥ π²/2` for the abstract
> `IsometricFilling`. Mathlib's `μH[2]` on the sup-norm plane `Fin 2 → ℝ` *is* Lebesgue
> measure (`hausdorffMeasure_pi_real`), and a 1-Lipschitz map does not increase `μH[2]`. So
> if the image of `quarterPairMap F` covers the filled diamond, `μH[2](M) ≥ π²/2 ≈ 4.93`.
> That needs no tangent planes. `DiamondGeometry` (below) adds injectivity of the boundary
> map and the area `π²/2`.

### `GromovFillingArea.DiamondGeometry` — diamond area `π²/2` & boundary injectivity

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `quarterDiamond` | `def` | `{p \| \|p 0 − π/2\| + \|p 1 − π/2\| ≤ π/2}` in `Fin 2 → ℝ` |
| `quarterDiamondBoundary` | `def` | the same set with `=` |
| `dist_coe_halfPi_of_le_neg` | theorem | `d(t, π/2) = t + 3π/2` for `t ∈ (−π, −π/2]` (period shift) (helper) |
| `dist_coe_halfPi_of_abs_le` | theorem | `d(t, π/2) = π/2 − t` for `t ∈ [−π/2, π/2]` (helper) |
| `dist_coe_halfPi_of_ge` | theorem | `d(t, π/2) = t − π/2` for `t ∈ [π/2, π]` (helper) |
| `abs_add_abs_le_iff` | theorem | `\|a\| + \|b\| ≤ r ↔ \|a + b\| ≤ r ∧ \|a − b\| ≤ r` (helper) |
| `quarterShear` | `def` | the shear `(a, b) ↦ (a + b, a − b)`, `Matrix.toLin' !![1, 1; 1, −1]` |
| `quarterShear_apply_zero` / `_one` | theorem | its coordinates (helpers) |
| `det_quarterShear` | theorem | `det quarterShear = −2` |
| `quarterDiamond_eq_preimage` | theorem | the diamond is the preimage of the box `[−π/2, π/2]²` under `p ↦ shear (p − (π/2, π/2))` |
| `quarterPairMap_boundary_injective` | theorem | `θ ↦ quarterPairMap F (F.ι θ)` is injective |
| `hausdorffMeasure_two_quarterDiamond` | theorem | `μH[2] quarterDiamond = π²/2` in the sup-norm plane |

**Injectivity.** Equal first coordinates give `|t₁| = |t₂|` for representatives
`t₁, t₂ ∈ (−π, π]`. If `t₁ = −t₂ ≠ t₂`, then equal second coordinates force `t₂ = 0` or
`t₂ = ±π`, and `±π` is outside `(−π, π]` on one side.

**Area.** This uses no Fubini integral. Translation by `−(π/2, π/2)` preserves `volume`, and
`addHaar_preimage_linearMap` gives `volume (shear⁻¹ box) = |det|⁻¹ · volume box`. So the
area is `½ · π · π = π²/2`, and `hausdorffMeasure_pi_real` turns `μH[2]` into `volume`.

### `GromovFillingArea.DiamondAreaBound` — diamond covering & universal `π²/2` bound

| Declaration | Kind | Statement |
| :--- | :--- | :--- |
| `diamondToComplex` | `def` | radial gauge map `Fin 2 → ℝ → ℂ`, `‖diamondToComplex p‖ = \|p 0 − π/2\| + \|p 1 − π/2\|` |
| `diamondVec`, `diamondGauge` | `def` | centred vector `(p 0 − π/2) + (p 1 − π/2) i` and `L¹` gauge |
| `diamondFromComplex` | `def` | inverse gauge `w ↦ (π/2, π/2) + (‖w‖ / (\|re w\| + \|im w\|)) (re w, im w)` |
| `diamondVec_re`, `diamondVec_im`, `diamondGauge_nonneg`, `diamondToComplex_eq`, `diamondVec_eq_zero_iff` | theorem | unfolding facts (helpers) |
| `norm_diamondToComplex` | theorem | `‖diamondToComplex p‖ = diamondGauge p` |
| `diamondFromComplex_diamondToComplex` | theorem | left inverse, hence `diamondToComplex_injective` |
| `diamondVec_diamondFromComplex`, `abs_re_add_abs_im_pos`, `diamondGauge_diamondFromComplex` | theorem | the inverse lands on gauge `‖w‖` (helpers) |
| `diamondToComplex_diamondFromComplex` | theorem | right inverse on `w ≠ 0` |
| `continuous_diamondToComplex` | theorem | continuous: a product of continuous maps off the centre, squeezed by the gauge at the centre |
| `quarterPairMap_boundary_apply` | theorem | `q(ι θ) = (d(θ, 0), d(θ, π/2))` |
| `diamondToComplex_boundary_mem_sphere` | theorem | the boundary lands on `sphere 0 (π/2)` |
| `exists_boundary_angle` | theorem | every diamond-boundary point is `q(ι θ)`, with `θ` explicit in each quadrant |
| `diamondToComplex_boundary_surjective` | theorem | the boundary map hits every point of `sphere 0 (π/2)` |
| `quarterDiamond_subset_range` | theorem | `quarterDiamond ⊆ range (quarterPairMap F)` |
| `gromov_universal_pi_sq_div_two_bound` | theorem | **main result:** every `F : IsometricFilling M` has `π²/2 ≤ μH[2] (univ : Set M)` |

`diamondToComplex` is not shown to be a homeomorphism `Fin 2 → ℝ ≃ₜ ℂ`; continuity and
injectivity are enough. The covering step then uses `Continuous.homeoOfEquivCompactToT2` on
the boundary circle and `disk_covered_of_no_retraction` with `F.no_boundary_retraction`.
This module compiled on its first build.

---

## Numerical Exploration (Genus 0–2)

`scripts/explore_genus2.py` is a numerical side experiment that runs alongside
the formal proofs. It builds orientable simplicial triangulations of genus
`g ∈ {0, 1, 2}` with one boundary cycle of `n_b = 16` vertices. Each starts as an
octahedron or a connected sum of 7-vertex tori. The script punches out one face,
does one midpoint subdivision, adds a collar out to a 16-ring, and then adds a
**second collar ring** of 4-split quads. Each mesh is checked for `χ = 1 − 2g`,
coherent orientation, manifold vertex links, and a single boundary cycle.

| Genus | V | E | F | Free edges | Faces / valence at each boundary vertex |
| :---: | :---: | :---: | :---: | :---: | :---: |
| 0 | 66 | 179 | 114 | 163 | 4 / 5 |
| 1 | 76 | 215 | 138 | 199 | 4 / 5 |
| 2 | 98 | 287 | 186 | 271 | 4 / 5 |

The metric is given by **intrinsic edge lengths**, a piecewise-flat Riemannian
metric with no embedding. Boundary edges are fixed at `2π/n_b`, so `∂M` has length
exactly `2π`. The script minimizes total Heron area subject to:

- strict triangle inequalities `ℓ_a + ℓ_b − ℓ_c ≥ 10⁻³` on every face;
- **boundary cone angles** `Σ (incident angles at b_i) ≥ π`, so the boundary is
  locally geodesic and no chord cuts a corner;
- the isometric boundary condition `d(b_i, b_j) ≥ d_{S¹}(b_i, b_j)`, where `d` is
  a shortest path on a **Steiner graph**. That graph has `k` points per edge,
  plus straight segments inside each face unfolded in the plane.

### Solver

There are 12 independent jobs (3 genera × 4 restarts), run in parallel on 8
cores.

1. **Strictly feasible start.** Each vertex gets a polar angle that decreases
   with its combinatorial depth, from `π/2` on the boundary toward the pole, and
   each edge gets the matching small step on the unit sphere. Restarts 1–3 draw
   a random depth exponent and jitter the interior polar angles. The interior
   lengths are scaled by the smallest `c` (found by bisection) at which every
   constraint holds. Every start is already strictly feasible.
2. **Powell** (`maxiter=2000`, up to 60 000 evaluations), then **adaptive
   Nelder-Mead** (20 000 evaluations). Both minimize
   Heron area `+ 10⁴ Σ max(0, d_{S¹} − d_{k=5})² + 10⁴ Σ max(0, π + 10⁻³ − ∠b_i)²`
   plus an extended log barrier on the triangle slacks.
3. **Restoration.** The script tries a radial rescale of the interior lengths
   and a blend back toward the start, each tuned by bisection. It keeps the
   cheaper of the two among points that pass every constraint with a `k = 16`
   violation `≤ 10⁻¹²`, i.e. zero up to floating-point roundoff.

**Certification.** A solution is certified when its `k = 16` violation is
`≤ 10⁻⁴`, the **exact corner-cut lower bound** is `0.0`, every triangle slack is
`≥ 10⁻³`, and every boundary angle is `≥ π`. All 12 restarts pass, and all 12
are also *strictly* feasible: the largest `k = 16` violation over all restarts is
`1.0·10⁻¹²`.

### Results

Results are in `benchmarks/genus_search.json`, which holds the full per-restart
telemetry and the final edge lengths. The run takes 18 min wall time on an M1
(4 performance + 4 efficiency cores):

```bash
.venv/bin/python3 scripts/explore_genus2.py --n-boundary 16 --maxiter 2000 --restarts 4
```

Here are the minimum areas over the four restarts. Every row has zero
violation: `k = 16` violation `≤ 10⁻¹²` and an exact lower bound of `0.0`.

| Filling | Best area `A` | `A / 2π` | Restart | Min boundary angle | Median fatness `2r/R` |
| :--- | :---: | :---: | :---: | :---: | :---: |
| g = 0, flat Tutte embedding in ℝ² (infeasible) | 3.10 | 0.49 | — | — | — |
| **g = 0** | **7.704** | **1.226** | 2 | 1.002 π | 0.57 |
| **g = 1** | **11.997** | **1.909** | 2 | 1.147 π | 0.82 |
| **g = 2** | **16.009** | **2.548** | 1 | 1.138 π | 0.82 |

The flat embedding has a `k = 16` violation of `1.13`.

Here is every restart. Each column is the area after that stage; every final
point is strictly feasible.

| g | r | Start | Powell | Nelder-Mead | Final `A` | `A / 2π` | Restoration |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :--- |
| 0 | 0 | 11.52 | 11.52 | 11.32 | 11.275 | 1.795 | scale 0.998 |
| 0 | 1 | 12.97 | 7.72 | 7.73 | 8.472 | 1.348 | blend `t = 0.069` |
| 0 | 2 | 12.92 | 7.50 | 7.41 | **7.704** | **1.226** | scale 1.022 |
| 0 | 3 | 12.61 | 12.61 | 11.64 | 11.764 | 1.872 | scale 1.006 |
| 1 | 0 | 12.68 | 12.68 | 12.53 | 12.517 | 1.992 | scale 1.000 |
| 1 | 1 | 14.46 | 14.46 | 14.01 | 13.840 | 2.203 | scale 0.993 |
| 1 | 2 | 12.24 | 12.24 | 11.67 | **11.997** | **1.909** | scale 1.015 |
| 1 | 3 | 12.51 | 12.51 | 12.12 | 12.159 | 1.935 | blend `t = 0.082` |
| 2 | 0 | 16.12 | 16.12 | 16.03 | 16.019 | 2.549 | scale 1.000 |
| 2 | 1 | 16.51 | 16.51 | 16.06 | **16.009** | **2.548** | scale 0.998 |
| 2 | 2 | 23.27 | 23.27 | 22.83 | 22.590 | 3.595 | scale 0.995 |
| 2 | 3 | 16.78 | 16.78 | 16.37 | 16.415 | 2.613 | scale 1.001 |

### What changed, and why it matters

Earlier collar meshes had boundary vertices that lay in only two faces. Their
cone angle was always `< π` (`0.88–0.91 π`), so a straight chord between the two
boundary neighbours cut the corner. That gave a true violation of `≈ 0.02` that
no amount of optimization could remove, and the `k = 8` check could not see it.
The second collar ring puts four faces at every boundary vertex, and the angle
penalty keeps every boundary angle `≥ π`. With that, the exact corner-cut bound
is `0.0` and the `k = 16` violation is at roundoff level. The best strictly
feasible areas (`7.70`, `12.00`, `16.01`) are also far below the previous
`k = 8`-only polished areas (`34.9`, `77.6`, `95.9`).

### Why flat fillings fail

A flat disk whose boundary has length `2π` has area at most `π`, the
isoperimetric maximum; the Tutte embedding here gives `3.10`. But its antipodal
boundary points are joined by a straight chord far shorter than the boundary
arc `π`, so `d ≥ d_{S¹}` fails by `≈ 1.1`. An isometric filling has to bulge out
of the plane. The round hemisphere does so with area exactly `2π ≈ 6.283`, and
the conjecture says nothing smaller is possible.

### What this run does and does not show

- It produces **strictly feasible** discrete fillings for g = 0, 1, 2. They have
  zero exact corner-cut bound, a `k = 16` violation `≤ 10⁻¹²`, every boundary
  angle `≥ π`, and well-shaped faces (median fatness `0.57–0.95`).
- Every area found is above `2π` (best genus 0: `1.226 · 2π`), as theory
  predicts for g = 0 (Pu/Ivanov) and g = 1 (Bangert–Croke–Ivanov–Katz).
- A Steiner graph only gives an *upper* bound on intrinsic distance. A zero
  `k = 16` reading is therefore strong numerical evidence of feasibility, not a
  proof.
- **The areas are not converged minima.** Powell stopped on its own tolerance
  after 1–3 sweeps (4 000–19 000 evaluations, well below its cap). For most
  restarts it made no progress from the start, which sits on the constraint
  boundary, and Nelder-Mead (in 163–271 dimensions) gains only a few percent.
  The spread across restarts (`7.70–11.76` for g = 0) shows how much depends on
  the start. Getting closer to the infimum would need gradient-based constrained
  optimization, finer meshes, and more restarts. The larger areas at higher
  genus come from these meshes and this optimizer, not from any proven bound.
  The gradient-based run below addresses the optimizer part of this.

### Gradient-Based Extremal Metric Discovery (Genus 0–2)

`scripts/discover_extremal_metrics.py` reruns the same search on the same meshes,
replacing Powell / Nelder-Mead with **L-BFGS-B using exact analytical
(sub)gradients** (`jac=True`). The optimizer never uses finite differences.

- **Heron area:** `∂A/∂ℓ_a = ℓ_a (ℓ_b² + ℓ_c² − ℓ_a²) / (8K)`, vectorized over faces.
- **Triangle log barrier** on `ℓ_a + ℓ_b − ℓ_c − 10⁻³`: `∂B/∂s = −10⁻² / s`. Below a slack
  of `10⁻³` it continues linearly, with a stiff `10⁸ · out²` quadratic. Truly invalid
  triangles return `10¹²`, so line searches back off. This is needed because Heron area
  has slope `∝ 1/√slack` as a face collapses. With the softer `10⁴` extension of
  `explore_genus2.py`, jittered restarts stepped into degenerate faces and stalled.
- **Boundary cone angles**, from the law of cosines: `∂α/∂a = a / 2K`,
  `∂α/∂b = −(b − c cos α) / 2K`. This makes `w Σ max(0, π + 10⁻³ − θ(b_i))²` smooth.
  The `10⁻³` margin matches `explore_genus2.py`.
- **Steiner distances (`k = 5`).** `dijkstra(..., return_predecessors=True)` gives the
  shortest-path tree. For every violated pair, the script walks the path back, and each
  segment adds `2w (d_5 − d_{S¹}) · ∂w_seg/∂ℓ` to the three edges of its face. Here
  `w_seg` is the segment's length in the face, unfolded in the plane.
  Where the shortest path is unique, this is the exact gradient.

`--check-grad` compares the full objective's gradient against central differences in
random directions, with every penalty active. The maximum relative error is
`1.6·10⁻⁸` (g = 0), `4.0·10⁻⁹` (g = 1) and `7.8·10⁻⁸` (g = 2).

**Schedule.** Each of the 12 parallel jobs (3 genera × 4 restarts, same seeds and
hemisphere-profile starts as above) runs three penalty stages, `w = 10², 10³, 10⁴`. Each
stage gets 3 000 L-BFGS-B iterations. Kinks where the shortest path switches make
L-BFGS-B stop early, so within a stage it is restarted with fresh memory until a cycle
gains less than `10⁻⁹`. **Feasibility polishing** reuses the rescale/blend bisection and
requires a `k = 16` violation `≤ 10⁻¹⁰`.

```bash
.venv/bin/python3 scripts/discover_extremal_metrics.py --n-boundary 16 --restarts 4
```

Results are in `benchmarks/extremal_discovery.json`. The run took 11.5 min wall time.
**All 12 restarts are strictly feasible:** `k = 16` violation `≤ 1.0·10⁻¹⁰`, exact
corner-cut lower bound `0.0`, every triangle slack `≥ 10⁻³`, and every boundary angle
`≥ π`.

| Filling | Best certified `A` | `A / 2π` | Restart | Powell/NM best (above) | Min boundary angle | Median fatness |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| **g = 0** | **6.361** | **1.012** | 0 | 7.704 | 1.008 π | 0.84 |
| **g = 1** | **6.658** | **1.060** | 0 | 11.997 | 1.013 π | 0.78 |
| **g = 2** | **7.009** | **1.116** | 0 | 16.009 | 1.015 π | 0.67 |

Every restart, with the area after each penalty stage and after polishing:

| g | r | Start | `w = 10²` | `w = 10³` | `w = 10⁴` | Final `A` | `A / 2π` | Polishing |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :--- |
| 0 | 0 | 11.52 | 6.269 | 6.268 | 6.268 | **6.361** | **1.012** | blend `t = 0.011` |
| 0 | 1 | 12.97 | 6.232 | 6.238 | 6.235 | 6.445 | 1.026 | blend `t = 0.021` |
| 0 | 2 | 12.92 | 6.195 | 6.198 | 6.197 | 6.595 | 1.050 | blend `t = 0.036` |
| 0 | 3 | 12.61 | 6.220 | 6.224 | 6.224 | 6.393 | 1.018 | scale 1.014 |
| 1 | 0 | 12.68 | 6.470 | 6.470 | 6.470 | **6.658** | **1.060** | blend `t = 0.018` |
| 1 | 1 | 14.46 | 6.416 | 6.409 | 6.403 | 6.824 | 1.086 | blend `t = 0.034` |
| 1 | 2 | 12.24 | 6.409 | 6.394 | 6.394 | 6.827 | 1.087 | scale 1.034 |
| 1 | 3 | 12.51 | 6.430 | 6.396 | 6.386 | 6.772 | 1.078 | blend `t = 0.035` |
| 2 | 0 | 16.12 | 6.661 | 6.655 | 6.657 | **7.009** | **1.116** | scale 1.026 |
| 2 | 1 | 16.51 | 6.457 | 6.408 | 6.407 | 7.567 | 1.204 | blend `t = 0.060` |
| 2 | 2 | 23.27 | 6.579 | 6.487 | 6.492 | 7.616 | 1.212 | blend `t = 0.040` |
| 2 | 3 | 16.78 | 6.561 | 6.552 | 6.552 | 7.330 | 1.167 | scale 1.059 |

**Structure of the extremal metrics.** The table splits each certified best metric into
two regions:

- **Handle region:** the subdivided punctured closed surface (a disk for g = 0).
- **Collar:** the fan collar plus the quad-strip ring.

| g | Handle area | Collar area | Handle / collar area | Handle share of `A` | Mean edge length handle / collar | Mean face area handle / collar |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| 0 | 1.663 | 4.697 | 0.354 | 26 % | 1.158 | 1.088 |
| 1 | 2.203 | 4.454 | 0.495 | 33 % | 1.134 | 0.818 |
| 2 | 3.323 | 3.687 | 0.901 | 47 % | 1.116 | 0.775 |

From g = 0 to g = 2, the handle region's area roughly doubles while the collar area
shrinks. The total grows by only `0.65`, because the handles absorb area the collar no
longer needs. Handle edges stay about 12–16 % longer than collar edges, yet handle faces
get relatively smaller (face-area ratio `1.09 → 0.78`). So the extra genus is packed
into many small, slightly elongated faces, not a few large ones. These ratios describe
these meshes and this optimizer, not a property of true minimizers.

**What this shows and does not show.**

- Exact gradients cut the best certified areas by 17 %, 45 % and 56 % compared with the
  derivative-free search. The best genus-0 area, `1.012 · 2π`, is within 1.3 % of the
  hemisphere.
- Every certified area is still `≥ 2π`. The penalized optima *before* polishing sit
  slightly below `2π` (`6.20–6.27` for g = 0), but those points violate the `k = 5`
  distances by `2–4·10⁻⁵`. Polishing to `k = 16` feasibility adds 1.5–18 % area.
  The fact that feasibility costs area is consistent with the conjecture.
- **Not converged.** Most stages hit the 3 000-iteration cap with the objective still
  creeping down. Final gradient sup-norms are `0.4–2.0`, not small, which is expected
  for a nonsmooth max-of-paths objective. Restart spread is `6.36–6.60` (g = 0) and `7.01–7.62` (g = 2).
- As above, a Steiner graph only upper-bounds intrinsic distance, so the certification
  is numerical evidence, not a proof.

## Neuro-Symbolic Invariant Discovery (Genus 0–2)

`scripts/conjecture_discovery.py` runs a closed-loop search for lower-bound functionals
`Φ(M) ≤ Area(M)`. It evaluates them on the 12 certified extremal metrics above plus
**200 strictly feasible random perturbations**. Each perturbation multiplies the free edge
lengths by log-normal noise of random size `σ ∈ [0.01, 0.15]` and is restored by
bisection. Of 258 attempts, 200 passed full re-certification: `k = 16` violation
`≤ 10⁻¹⁰`, corner-cut bound `0`, triangle slacks, and boundary angles `≥ π`. That gives
212 meshes, with areas `6.36–6.71` (g = 0, 72 meshes), `6.66–6.89` (g = 1, 72) and
`7.01–7.68` (g = 2, 68).

```bash
.venv/bin/python3 scripts/conjecture_discovery.py --n-perturb 200   # ≈ 8 min on 8 cores
```

Results are in `benchmarks/conjecture_discovery.json`, which holds every functional's
statistics, the per-mesh features, and the calibration weights.

**Features.** For each mesh the script computes:

- the Kuratowski matrix `D[v, j] = d_int(v, b_j)`, by `k = 16` Steiner Dijkstra;
- discrete Fourier coefficients `f̂[v, m]`;
- per-face PL gradients of every coordinate on coherently oriented face charts, which
  give Jacobians `det J_f` and the calibration 2-forms `∫_f dx_i ∧ dx_j`;
- antipodal excess `D[v, j] + D[v, j + n/2] − π`, and depth `min_j D[v, j]`.

**Pipeline checks:**

- **Stokes.** The face-by-face integrals `∫_M dx_i ∧ dx_j` match the boundary integrals
  `∮ x_i dx_j` of the exact tent profiles to `3.9·10⁻¹¹` on every mesh.
- **Boundary rows.** The boundary rows of `D` match `d_{S¹}` to `10⁻¹⁰`.
- **Antipodal excess.** It is never below `−10⁻¹⁰`, as the `AntipodalRadius` theorem
  requires.

**Library (59 functionals, four families).**

| Family | Count | Examples | Why `Φ ≤ Area` might hold |
| :--- | :---: | :--- | :--- |
| `proof-sketch` | 30 | `\|∫ dx_0 ∧ dx_s\|` for each separation `s`; Fourier-mode calibrations `\|∫ det D f̂_m\|` at Lipschitz constant 1 and at the sharp constant; `√2`-Parseval Kähler sums `2 Σ w_m \|I_m\|`; optimal weighted pair calibration `\|Σ w_ij ∫ dx_i ∧ dx_j\| / comass(w)` | Every coordinate map is 1-Lipschitz and every form has comass `≤ 1`, so `\|F*ω\| ≤ dA` pointwise on a Riemannian filling. By Stokes these values depend only on the boundary and are identical on every mesh. |
| `mesh-sound-if-1-Lipschitz` | 15 | unsigned calibrations `∫ \|dx_i ∧ dx_{i+s}\|`, coarea `∫ \|∇δ\|`, Kuratowski Dirichlet energy `∫ mean_j \|∇x_j\|²`, spectral Hilbert–Schmidt energies | Only if the PL gradients have norm `≤ 1` |
| `heuristic` | 8 | `c · inradius²`, antipodal-excess integrals, `1.1 ×` Dirichlet energy | No argument |
| `control` | 6 | constants `4/π`, `π`, `7ζ(3)/π`, `π²/2`, `14ζ(3)/π`, `2π` | Calibrates the filter itself |

**Soundness filter.** 52 functionals never exceed `Area(M)` on any of the 212 meshes. The
7 violated ones are:

| Functional | Family | Violations / 212 | `Φ / Area` range |
| :--- | :--- | :---: | :---: |
| `kuratowski_dirichlet_1.1` | heuristic | 212 | 1.093–1.420 |
| `max_gradient` (`∫ max_j \|∇x_j\|`) | mesh-sound-if-1-Lip | 212 | 1.126–1.450 |
| `inradius_sq_4` | heuristic | 212 | 1.101–1.437 |
| `kuratowski_dirichlet_1.0` | mesh-sound-if-1-Lip | 174 | 0.993–1.291 |
| `coarea_depth` | mesh-sound-if-1-Lip | 140 | 0.981–1.109 |
| `inradius_sq_pi` | heuristic | 74 | 0.864–1.129 |
| `kuratowski_dirichlet_0.9` | mesh-sound-if-1-Lip | 51 | 0.894–1.162 |

The mesh-dependent failures come from discretization, not counterexamples. PL
interpolation of the distance functions on these coarse meshes is not 1-Lipschitz:

- the median PL gradient norm is `0.9996`, but the maximum is `14.3` on sliver faces;
- 20 % of face-coordinate gradients exceed `1.05`.

**Ranking.** The sound functionals ranked by worst-case tightness `min_M Φ / Area`:

| Rank | Functional | Family | `min Φ` | Tightness `min Φ/A` | `min Φ / (4/π)` | `min Φ / (14ζ(3)/π)` |
| :---: | :--- | :--- | :---: | :---: | :---: | :---: |
| 1 | `constant_2pi` | control | 6.2832 | 0.818 | 4.935 | 1.173 |
| 2 | `unsigned_pair_s4` | mesh-dependent | 4.9457 | 0.749 | 3.884 | 0.923 |
| 3 | `unsigned_pair_s5` | mesh-dependent | 4.6575 | 0.710 | 3.658 | 0.869 |
| 4 | `inradius_sq_8/pi` | heuristic | 4.7117 | 0.701 | 3.701 | 0.880 |
| 5 | `constant_14zeta(3)/pi` | control | 5.3568 | 0.697 | 4.207 | 1.000 |
| 6 | **`calibration_lp_n2048`** | proof-sketch | **5.3568** | 0.697 | **4.207** | **1.000** |
| 8 | **`calibration_lp`** (`n = 16`) | proof-sketch | **5.3246** | 0.693 | 4.182 | 0.994 |
| 9 | `calibration_sign` | proof-sketch | 5.1034 | 0.664 | 4.008 | 0.953 |
| 12 | `pair_calibration_s4` | proof-sketch | 4.9348 `= π²/2` | 0.643 | 3.876 | 0.921 |
| 24 | `fourier_mode1_sharp_lip` | proof-sketch | 3.1011 (`→ π`) | 0.404 | 2.436 | 0.579 |
| 27 | `kahler_flat_upto7` | proof-sketch | 2.6623 (`→ 7ζ(3)/π`) | 0.347 | 2.091 | 0.497 |
| 41 | `fourier_mode1_lip1` | proof-sketch | 1.2731 (`= 4/π`) | 0.166 | 1.000 | 0.238 |

The top of this ranking shows the limit of the method. **`constant_2pi`, which *is* the
conjecture, passes the empirical filter and ranks first.** Every mesh here has area
`≥ 6.36`, so empirical soundness says nothing about whether a bound holds for all
fillings. Only the `proof-sketch` rows carry an argument.

**What the search found.**

1. **The optimal Kuratowski calibration has value `14ζ(3)/π`.** The best constant-
   coefficient 2-form `Σ_{i<j} w_ij dx_i ∧ dx_j` can be found exactly:
   - The boundary invariant `I_ij = ∮ x_i dx_j` is rotation invariant, and comass is a
     rotation-invariant norm, so averaging over rotations shows the optimum is a
     circulant `w_ij = a_{j−i}`.
   - For a circulant form, the top eigenvector of `−iW` is a Fourier phase vector of unit
     modulus. So the spectral upper bound on the comass is attained, and the comass is
     exact. Multi-start ascent reproduces it: `16.000000` vs `16`.
   - The search is then a 7-variable LP for `n = 16`.

   Its optimum is `5.3246`. Repeating the same LP with `n = 32, …, 2048` boundary points
   gives `5.3486, 5.3547, 5.3563, 5.35664, 5.35674, 5.356764, 5.356770`.
   Richardson extrapolation gives `5.3567723`, which equals the repo's target constant
   `14ζ(3)/π = 5.3567723` to all 7 digits shown. The optimal weights converge to
   `a_s = 4/(πs)` for odd `s` and `0` for even `s`, the square-wave Fourier coefficients
   that pair with the `Σ_{odd} 1/k³ = (7/8) ζ(3)` series of `ZetaBound`. The
   identification of the limit is numerical, not proved.
2. **One antipodal-quarter pair already gives `π²/2`.** The map
   `(d(·, b_0), d(·, b_4))` has 1-Lipschitz coordinates, so `|dx ∧ dy| ≤ 1`, and its
   boundary curve encloses a square of area `π²/2 ≈ 4.935`. The same map is 1-Lipschitz
   into the *sup-norm* plane, where `μH[2]` is Lebesgue area, so a covering argument
   gives this bound without tangent planes. It is now the kernel-checked main theorem
   `gromov_universal_pi_sq_div_two_bound`, formalized across `QuarterCircleSquare`,
   `DiamondGeometry` and `DiamondAreaBound`.
3. **The formal `4/π` argument has slack (now formalized).** For each pair `x, y`,
   `|f̂_x(1) − f̂_y(1)| ≤ (2/π) d(x, y)`, because `(1/2π) ∫ |cos| = 2/π`, not `1`. So
   `(π/2) · f̂(1)` is Euclidean 1-Lipschitz, and the same covering argument as
   `UniversalAreaBound` gives `π` instead of `4/π`. The discrete value is `3.1011` at
   `n = 16` and converges to `π`. Like item 2 and unlike item 1, this needs no tangent planes, so it
   fits the abstract metric-space `IsometricFilling` of `Basic.lean` directly. It is now
   the kernel-checked `gromov_universal_pi_bound` in `SharpFirstMode`.

**What this does and does not show.**

- Items 2 and 3 are proved for the abstract `IsometricFilling`. Item 1 is a **proof sketch for
  Riemannian, orientable fillings**: a weighted sum of many pairs needs a.e.
  differentiability (2-dimensional tangent planes, `|∇ d(·, b)| ≤ 1`) and Stokes on an
  oriented surface, neither of which is part of the abstract `IsometricFilling`. Whether
  these bounds are already in the literature was not checked.
- Every proof-sketch bound is `≤ 2π`, as it must be (the hemisphere has area `2π`). The
  best, `14ζ(3)/π ≈ 0.853 · 2π`, is the ceiling of constant-coefficient pair
  calibrations, so closing the gap to `2π` needs different forms or maps.
- Empirical soundness on 212 near-extremal meshes is weak evidence. Every mesh-dependent
  functional is confounded by PL gradient overshoot, and the genus has no visible effect
  on any proof-sketch functional, because those depend only on the boundary.

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
  Basic.lean           # Circle2Pi, IsometricFilling (incl. no retraction), conjecture
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
  UniversalAreaBound.lean # Area(M) ≥ 4/π for every IsometricFilling (superseded)
  PuSymmetrization.lean # hemisphere area 2π; sin ≤ φ on [0, π/2] ⇒ 2π ∫ φ ≥ 2π
  ConformalPuBound.lean # (mean λ)² ≤ mean λ²; angular averaging never increases area
  RadialGeodesicBound.lean # antipodal ray sum ≥ π ⇒ symmetrized radial radius ≥ π/2
  ConformalDiskArea.lean # λ = 2/(1+r²): inradius π/2, conformal area 2π
  HemisphereCalibration.lean # mean λ ≥ 2/(1+r²) on [0, 1] ⇒ conformal area ≥ 2π
  WeightedRadialBound.lean # 2π + 4π · (calibration moment) ≤ area; moment ≥ 0 ⇒ area ≥ 2π
  ConformalBoundaryLength.lean # 2π ≤ L ↔ 1 ≤ mean λ(1); ∫ r h² ≤ ∫ r h · mean λ ⇒ area ≥ 2π
  SharpFirstMode.lean  # f̂(1) is (2/π)-Lipschitz ⇒ Area(M) ≥ π (superseded)
  QuarterCircleSquare.lean # 1-Lipschitz (f_x(0), f_x(π/2)); ∂M ↦ L¹ diamond of area π²/2
  DiamondGeometry.lean # μH[2] diamond = π²/2 (shear, det −2); boundary map injective
  DiamondAreaBound.lean # diamond covering ⇒ main theorem Area(M) ≥ π²/2
GromovFillingArea.lean # root module re-exporting all verified modules
CLAUDE.md              # agent protocol (compiler-in-the-loop rules)
scripts/
  verify_and_log.py    # lake-build oracle + JSONL telemetry
  generate_report.py   # benchmark table generator
  explore_genus2.py    # genus 0–2 discrete filling-area search (numerical)
  discover_extremal_metrics.py # L-BFGS-B with exact (sub)gradients, genus 0–2
  conjecture_discovery.py # lower-bound functional search; optimal calibration → 14ζ(3)/π
benchmarks/results.jsonl
benchmarks/genus_search.json
benchmarks/extremal_discovery.json
benchmarks/conjecture_discovery.json
.github/workflows/lean_action_ci.yml
```

## Roadmap

- Replace the abstract orientability `Prop` with a genuine 2-manifold structure.
- Fourier-coefficient decay for 1-Lipschitz periodic functions, and the Wirtinger
  energy inequality.
- Combine these into a formal (non-sharp) universal area lower bound.
- Formalize the optimal pair calibration (`14ζ(3)/π` in the limit) from Neuro-Symbolic
  Invariant Discovery. This needs a.e. differentiability and Stokes, which the abstract
  `IsometricFilling` does not provide.
- Extend the telemetry with token counts and attempt-level diffs, so that
  different prover models can be compared on the same harness.

## License

Apache 2.0. See file headers.

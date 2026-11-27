/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.AreaContraction

/-!
# 1-Lipschitz Fourier Mode Projections & Projected Disk Area

This file defines the `n`-th Fourier mode projection `(Circle2Pi →ᵇ ℝ) → ℂ`,
proves that it is `1`-Lipschitz (`LipschitzWith 1`), and deduces via
`kuratowskiBanach_proj_hausdorffMeasure_le` that the `2`-dimensional Hausdorff
area of the `n`-th Fourier image of `M` in `ℂ` is bounded above by `Area(M)`.
-/

open MeasureTheory Metric Set BoundedContinuousFunction AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The `n`-th Fourier coefficient projection from `Circle2Pi →ᵇ ℝ` to `ℂ`. -/
def fourierProj (n : ℤ) (g : Circle2Pi →ᵇ ℝ) : ℂ :=
  fourierCoeff (fun θ : Circle2Pi => (g θ : ℂ)) n

/-- The complexification `θ ↦ (g θ : ℂ)` of a bounded continuous `g` is continuous. -/
theorem bcf_complex_continuous (g : Circle2Pi →ᵇ ℝ) :
    Continuous (fun θ : Circle2Pi => (g θ : ℂ)) :=
  Complex.continuous_ofReal.comp g.continuous

/-- **Lemma 1 (1-Lipschitz Property of Fourier Coefficient Projections):**
For every frequency `n : ℤ`, `fourierProj n : (Circle2Pi →ᵇ ℝ) → ℂ` is `1`-Lipschitz. -/
theorem fourierProj_lipschitzWith (n : ℤ) :
    LipschitzWith 1 (fourierProj n) := by
  refine LipschitzWith.of_dist_le_mul fun g h => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, fourierProj, fourierProj,
    ← fourierCoeff_sub_of_continuous _ _ (bcf_complex_continuous g) (bcf_complex_continuous h)]
  refine fourierCoeff_norm_le_of_norm_le _ _ (fun θ => ?_) n
  show ‖(g θ : ℂ) - (h θ : ℂ)‖ ≤ ‖g - h‖
  rw [← Complex.ofReal_sub, Complex.norm_real]
  exact (g - h).norm_coe_le_norm θ

/-- **Lemma 2 (Harmonic Projection Area Contraction):**
For every frequency `n : ℤ`, the `2`-dimensional Hausdorff measure of the `n`-th
Fourier projection `{f̂_x(n) | x : M}` in `ℂ` is at most `hausdorffMeasure 2 (univ : Set M)`. -/
theorem kuratowski_fourierProj_hausdorffMeasure_le (F : IsometricFilling M) (n : ℤ) :
    MeasureTheory.Measure.hausdorffMeasure 2 (range (fourierProj n ∘ kuratowskiBanach F)) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) :=
  kuratowskiBanach_proj_hausdorffMeasure_le F (fourierProj n) (fourierProj_lipschitzWith n)

end

end

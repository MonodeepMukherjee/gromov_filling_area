/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.StokesCalibration

/-!
# Multi-Mode `ℓ¹`-Normalized Fourier Calibration Maps on `IsometricFilling`

This file constructs the multi-harmonic Fourier calibration map
`multiFourierProj w : (Circle2Pi →ᵇ ℝ) → ℂ` defined by
`g ↦ ∑ n ∈ S, w n * fourierProj n g` for any finite set of frequencies `S : Finset ℤ`
and weights `w : ℤ → ℂ` with `∑ n ∈ S, ‖w n‖ ≤ 1`. It proves that `multiFourierProj w`
is `1`-Lipschitz (`LipschitzWith 1`) and deduces via
`kuratowskiBanach_proj_hausdorffMeasure_le` that the `2`-dimensional Hausdorff area of
`range (multiFourierProj w ∘ kuratowskiBanach F)`
is bounded above by `hausdorffMeasure 2 (univ : Set M)`.
-/

open MeasureTheory Metric Set BoundedContinuousFunction AddCircle Finset

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Multi-mode Fourier projection `g ↦ ∑ n ∈ S, w n * fourierProj n g` into `ℂ`. -/
def multiFourierProj (S : Finset ℤ) (w : ℤ → ℂ) (g : Circle2Pi →ᵇ ℝ) : ℂ :=
  ∑ n ∈ S, w n * fourierProj n g

/-- **Lemma 1 (1-Lipschitz Property of `ℓ¹`-Normalized Multi-Mode Projections):**
If `∑ n ∈ S, ‖w n‖ ≤ 1`, then `multiFourierProj S w : (Circle2Pi →ᵇ ℝ) → ℂ` is `1`-Lipschitz. -/
theorem multiFourierProj_lipschitzWith (S : Finset ℤ) (w : ℤ → ℂ)
    (hw : ∑ n ∈ S, ‖w n‖ ≤ 1) :
    LipschitzWith 1 (multiFourierProj S w) := by
  refine LipschitzWith.of_dist_le_mul fun g h => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, multiFourierProj, multiFourierProj,
    ← Finset.sum_sub_distrib]
  calc ‖∑ n ∈ S, (w n * fourierProj n g - w n * fourierProj n h)‖
      ≤ ∑ n ∈ S, ‖w n * fourierProj n g - w n * fourierProj n h‖ := norm_sum_le _ _
    _ = ∑ n ∈ S, ‖w n‖ * dist (fourierProj n g) (fourierProj n h) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← mul_sub, norm_mul, dist_eq_norm]
    _ ≤ ∑ n ∈ S, ‖w n‖ * dist g h := by
        refine Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        simpa using (fourierProj_lipschitzWith n).dist_le_mul g h
    _ = (∑ n ∈ S, ‖w n‖) * dist g h := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * dist g h := mul_le_mul_of_nonneg_right hw dist_nonneg
    _ = dist g h := one_mul _

/-- **Lemma 2 (Multi-Mode Calibration Area Contraction on `IsometricFilling`):**
For every `F : IsometricFilling M` and every `ℓ¹`-normalized weight family
`∑ n ∈ S, ‖w n‖ ≤ 1`, the `2`-dimensional Hausdorff measure of
`range (multiFourierProj S w ∘ kuratowskiBanach F)` is at most `μH (univ : Set M)`. -/
theorem kuratowski_multiFourierProj_hausdorffMeasure_le (F : IsometricFilling M)
    (S : Finset ℤ) (w : ℤ → ℂ) (hw : ∑ n ∈ S, ‖w n‖ ≤ 1) :
    MeasureTheory.Measure.hausdorffMeasure 2
        (range (multiFourierProj S w ∘ kuratowskiBanach F)) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) :=
  kuratowskiBanach_proj_hausdorffMeasure_le F (multiFourierProj S w)
    (multiFourierProj_lipschitzWith S w hw)

end

end

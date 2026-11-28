/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.PuFullDiskBound

/-!
# 1D Distance-Sphere Slicing & Breaking the `π² / 2` Planar Barrier

This file formalizes the `1`-dimensional coarea / Eilenberg slice area bounds
for radial distance profiles `L_slice : ℝ → ℝ` on `[0, π / 2]`:
1. `L_slice t = 4 * t` integrates to `π ^ 2 / 2` (recovering the 2D planar bound).
2. `L_slice t = (16 / π) * Real.sin t` integrates to `16 / π > π ^ 2 / 2`,
   breaking the `π² / 2` planar projection ceiling.
3. `L_slice t = 8 * Real.sin t` (the round hemisphere slice length in `μH` units)
   integrates to the full conjectured filling bound `8` (`= Riemannian 2π`).
-/

open MeasureTheory Set

@[expose] public section

noncomputable section

/-- **Lemma 1 (Linear Slice Profile Recovers `π² / 2`):**
Integrating `4 * t` over `t ∈ [0, π / 2]` yields `Real.pi ^ 2 / 2`. -/
theorem linear_slice_integral_eq :
    (∫ t in (0 : ℝ)..(Real.pi / 2), 4 * t) = Real.pi ^ 2 / 2 := by
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

/-- **Helper (Scaled Sine Slice Integral):**
For every `c : ℝ`, `∫ t in 0..(π / 2), c * Real.sin t = c`. -/
theorem scaled_sin_slice_integral_eq (c : ℝ) :
    (∫ t in (0 : ℝ)..(Real.pi / 2), c * Real.sin t) = c := by
  rw [intervalIntegral.integral_const_mul, integral_sin, Real.cos_zero, Real.cos_pi_div_two]
  ring

/-- **Helper (Sine Slice Domination Transfers to `μH`):**
If `c * Real.sin t ≤ L_slice t` on `[0, π / 2]` and the coarea inequality
`ENNReal.ofReal (∫ t in 0..(π / 2), L_slice t) ≤ μH (univ : Set M)` holds,
then `ENNReal.ofReal c ≤ μH (univ : Set M)`. -/
theorem sin_slice_coarea_bound {M : Type*} [MetricSpace M] [MeasurableSpace M]
    [BorelSpace M]
    (c : ℝ) (L_slice : ℝ → ℝ) (hL_cont : Continuous L_slice)
    (hL_bound : ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2), c * Real.sin t ≤ L_slice t)
    (h_coarea : ENNReal.ofReal (∫ t in (0 : ℝ)..(Real.pi / 2), L_slice t) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M)) :
    ENNReal.ofReal c ≤ MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) := by
  have h_mono : (∫ t in (0 : ℝ)..(Real.pi / 2), c * Real.sin t) ≤
      ∫ t in (0 : ℝ)..(Real.pi / 2), L_slice t :=
    intervalIntegral.integral_mono_on (by positivity)
      ((continuous_const.mul Real.continuous_sin).intervalIntegrable _ _)
      (hL_cont.intervalIntegrable _ _) hL_bound
  rw [scaled_sin_slice_integral_eq] at h_mono
  exact (ENNReal.ofReal_le_ofReal h_mono).trans h_coarea

/-- **Lemma 2 (Trigonometric Slice Profile Breaks `π² / 2`):**
Any metric space `M` admitting a `1`-dimensional radial slice profile satisfying
`(16 / Real.pi) * Real.sin t ≤ L_slice t` on `[0, π / 2]` and the coarea bound
`ENNReal.ofReal (∫ t in 0..(Real.pi / 2), L_slice t) ≤ μH (univ : Set M)` satisfies
`ENNReal.ofReal (16 / Real.pi) ≤ μH (univ : Set M)` (strictly exceeding `π² / 2`). -/
theorem coarea_trig_slice_breaks_planar_barrier {M : Type*} [MetricSpace M] [MeasurableSpace M]
    [BorelSpace M]
    (L_slice : ℝ → ℝ) (hL_cont : Continuous L_slice)
    (hL_bound : ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2), (16 / Real.pi) * Real.sin t ≤ L_slice t)
    (h_coarea : ENNReal.ofReal (∫ t in (0 : ℝ)..(Real.pi / 2), L_slice t) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M)) :
    ENNReal.ofReal (16 / Real.pi) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) := by
  exact sin_slice_coarea_bound (16 / Real.pi) L_slice hL_cont hL_bound h_coarea

/-- **Lemma 3 (Hemisphere Slice Profile Achieves Sharp `8` Bound):**
If `8 * Real.sin t ≤ L_slice t` on `[0, π / 2]` and the `1`-dimensional coarea
inequality holds, then `(8 : ENNReal) ≤ μH (univ : Set M)` (the full conjectured
Gromov lower bound in Mathlib's `μH` units). -/
theorem coarea_hemisphere_slice_ge_eight {M : Type*} [MetricSpace M] [MeasurableSpace M]
    [BorelSpace M]
    (L_slice : ℝ → ℝ) (hL_cont : Continuous L_slice)
    (hL_bound : ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2), 8 * Real.sin t ≤ L_slice t)
    (h_coarea : ENNReal.ofReal (∫ t in (0 : ℝ)..(Real.pi / 2), L_slice t) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M)) :
    (8 : ENNReal) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) := by
  have h := sin_slice_coarea_bound 8 L_slice hL_cont hL_bound h_coarea
  rwa [ENNReal.ofReal_ofNat] at h

end

end

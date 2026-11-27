/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.ConformalDiskArea

/-!
# Stereographic Hemisphere Calibration & Conformal Disk `2π` Lower Bound

This file proves the quadratic calibration inequality around the stereographic
hemisphere profile `hemisphereConformalFactor r = 2 / (1 + r ^ 2)` and combines
it with `ConformalPuBound` to prove that every conformal disk metric
`λ(r, θ)² (dr² + r² dθ²)` whose angular average satisfies
`hemisphereConformalFactor r ≤ angularMean (λ r)` on `[0, 1]` has area at least `2π`.
-/

open MeasureTheory Set

@[expose] public section

noncomputable section

/-- **Lemma 1 (Pointwise Hemisphere Calibration Inequality):**
For `0 ≤ r` and any `u : ℝ`, writing `h = hemisphereConformalFactor r`,
`r * h ^ 2 + 2 * r * h * (u - h) ≤ r * u ^ 2`. -/
theorem hemisphere_calibration_pointwise {r : ℝ} (hr : 0 ≤ r) (u : ℝ) :
    r * (hemisphereConformalFactor r) ^ 2 +
      2 * r * hemisphereConformalFactor r * (u - hemisphereConformalFactor r) ≤
      r * u ^ 2 := by
  nlinarith [mul_nonneg hr (sq_nonneg (u - hemisphereConformalFactor r))]

/-- **Lemma 2 (Sharp `2π` Area Bound for Conformal Disks):**
For any jointly continuous conformal factor `lam : ℝ → ℝ → ℝ` on `[0, 1] × [0, 2π]`
whose angular mean satisfies `hemisphereConformalFactor r ≤ angularMean (lam r)` for
all `r ∈ [0, 1]`, the total conformal area
`2 * π * ∫ r in 0..1, r * angularMean (fun θ => (lam r θ) ^ 2)` is at least `2 * π`. -/
theorem conformal_disk_area_ge_two_pi (lam : ℝ → ℝ → ℝ)
    (hlam_cont : Continuous (Function.uncurry lam))
    (hlam_dom : ∀ r ∈ Icc (0 : ℝ) 1, hemisphereConformalFactor r ≤ angularMean (lam r)) :
    2 * Real.pi ≤
      2 * Real.pi * (∫ r in (0 : ℝ)..(1 : ℝ), r * angularMean (fun θ => (lam r θ) ^ 2)) := by
  have hh_cont : Continuous hemisphereConformalFactor :=
    continuous_const.div (by fun_prop) (fun r => by positivity)
  have hh_nonneg : ∀ r, 0 ≤ hemisphereConformalFactor r := fun r => by
    unfold hemisphereConformalFactor; positivity
  have hmean_cont : Continuous (fun r => angularMean (lam r)) :=
    continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hlam_cont _ _)
  have hmean_sq_cont : Continuous (fun r => angularMean (fun θ => (lam r θ) ^ 2)) :=
    continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun r θ => (lam r θ) ^ 2) (by exact hlam_cont.pow 2) _ _)
  -- Step 1: the hemisphere profile is dominated by the averaged profile.
  have h_step1 : (∫ r in (0 : ℝ)..(1 : ℝ), r * (hemisphereConformalFactor r) ^ 2) ≤
      ∫ r in (0 : ℝ)..(1 : ℝ), r * (angularMean (lam r)) ^ 2 := by
    refine intervalIntegral.integral_mono_on zero_le_one
      ((continuous_id.mul (hh_cont.pow 2)).intervalIntegrable _ _)
      ((continuous_id.mul (hmean_cont.pow 2)).intervalIntegrable _ _) ?_
    intro r hr
    have hcal := hemisphere_calibration_pointwise hr.1 (angularMean (lam r))
    have hcross : 0 ≤ 2 * r * hemisphereConformalFactor r *
        (angularMean (lam r) - hemisphereConformalFactor r) :=
      mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hr.1) (hh_nonneg r))
        (sub_nonneg.mpr (hlam_dom r hr))
    linarith
  -- Step 2: rotational symmetrization never increases area.
  have h_step2 := radial_symmetrized_area_le (fun r => r) continuous_id
    (fun r hr => hr.1) lam (fun r => hlam_cont.uncurry_left r)
    (continuous_id.mul hmean_sq_cont)
  calc 2 * Real.pi
      = 2 * Real.pi * (∫ r in (0 : ℝ)..(1 : ℝ), r * (hemisphereConformalFactor r) ^ 2) :=
        hemisphere_conformal_area.symm
    _ ≤ 2 * Real.pi * (∫ r in (0 : ℝ)..(1 : ℝ), r * angularMean (fun θ => (lam r θ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (h_step1.trans h_step2) Real.two_pi_pos.le

end

end

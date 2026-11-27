/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.HemisphereCalibration

/-!
# Integrated Hemisphere Calibration & Moment-Condition `2π` Bound

This file integrates the quadratic calibration inequality around
`h(r) = hemisphereConformalFactor r = 2 / (1 + r ^ 2)` over `[0, 1]`, proving that
any continuous conformal disk metric `lam` satisfies
`2 * π + 4 * π * ∫ r in 0..1, r * h r * (angularMean (lam r) - h r) ≤ Area(lam)`.
Consequently, a single vanishing/non-negative first radial moment against `r * h(r)`
suffices to guarantee the sharp `2 * π` area bound—replacing pointwise dominance
`h(r) ≤ angularMean (lam r)` by a single global integral condition.
-/

open MeasureTheory Set

@[expose] public section

noncomputable section

/-- **Lemma 1 (Integrated Calibration Lower Bound for Conformal Disks):**
For any jointly continuous conformal factor `lam : ℝ → ℝ → ℝ` on `[0, 1] × [0, 2π]`,
writing `h = hemisphereConformalFactor`,
`2 * π + 4 * π * ∫ r in 0..1, r * h r * (angularMean (lam r) - h r)`
is at most the conformal area `2 * π * ∫ r in 0..1, r * angularMean (fun θ => (lam r θ) ^ 2)`. -/
theorem conformal_disk_calibrated_area_bound (lam : ℝ → ℝ → ℝ)
    (hlam_cont : Continuous (Function.uncurry lam)) :
    2 * Real.pi +
      4 * Real.pi *
        (∫ r in (0 : ℝ)..(1 : ℝ),
          r * hemisphereConformalFactor r * (angularMean (lam r) - hemisphereConformalFactor r)) ≤
      2 * Real.pi * (∫ r in (0 : ℝ)..(1 : ℝ), r * angularMean (fun θ => (lam r θ) ^ 2)) := by
  set h := hemisphereConformalFactor with hh_def
  have hh_cont : Continuous h :=
    continuous_const.div (by fun_prop) (fun r => by positivity)
  have hmean_cont : Continuous (fun r => angularMean (lam r)) :=
    continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hlam_cont _ _)
  have hmean_sq_cont : Continuous (fun r => angularMean (fun θ => (lam r θ) ^ 2)) :=
    continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun r θ => (lam r θ) ^ 2) (by exact hlam_cont.pow 2) _ _)
  have hI1 : IntervalIntegrable (fun r => r * h r ^ 2) volume 0 1 :=
    (continuous_id.mul (hh_cont.pow 2)).intervalIntegrable _ _
  have hM : IntervalIntegrable
      (fun r => r * h r * (angularMean (lam r) - h r)) volume 0 1 :=
    ((continuous_id.mul hh_cont).mul (hmean_cont.sub hh_cont)).intervalIntegrable _ _
  -- Integrate the pointwise calibration over `[0, 1]`.
  have h_cal : (∫ r in (0 : ℝ)..(1 : ℝ),
      r * h r ^ 2 + 2 * (r * h r * (angularMean (lam r) - h r))) ≤
      ∫ r in (0 : ℝ)..(1 : ℝ), r * (angularMean (lam r)) ^ 2 := by
    refine intervalIntegral.integral_mono_on zero_le_one (hI1.add (hM.const_mul 2))
      ((continuous_id.mul (hmean_cont.pow 2)).intervalIntegrable _ _) ?_
    intro r hr
    have := hemisphere_calibration_pointwise hr.1 (angularMean (lam r))
    linarith
  rw [intervalIntegral.integral_add hI1 (hM.const_mul 2),
    intervalIntegral.integral_const_mul] at h_cal
  -- Rotational symmetrization never increases area.
  have h_sym := radial_symmetrized_area_le (fun r => r) continuous_id
    (fun r hr => hr.1) lam (fun r => hlam_cont.uncurry_left r)
    (continuous_id.mul hmean_sq_cont)
  have h_mul := mul_le_mul_of_nonneg_left (h_cal.trans h_sym) Real.two_pi_pos.le
  have h_area := hemisphere_conformal_area
  rw [← hh_def] at h_area
  linarith

/-- **Lemma 2 (Sharp `2π` Bound from Non-Negative Calibration Moment):**
If `0 ≤ ∫ r in 0..1, r * h r * (angularMean (lam r) - h r)` with
`h = hemisphereConformalFactor`, then the conformal disk area is at least `2 * π`. -/
theorem conformal_disk_area_ge_two_pi_of_moment (lam : ℝ → ℝ → ℝ)
    (hlam_cont : Continuous (Function.uncurry lam))
    (h_moment : 0 ≤ ∫ r in (0 : ℝ)..(1 : ℝ),
      r * hemisphereConformalFactor r * (angularMean (lam r) - hemisphereConformalFactor r)) :
    2 * Real.pi ≤
      2 * Real.pi * (∫ r in (0 : ℝ)..(1 : ℝ), r * angularMean (fun θ => (lam r θ) ^ 2)) := by
  have h := conformal_disk_calibrated_area_bound lam hlam_cont
  nlinarith [Real.pi_pos]

end

end

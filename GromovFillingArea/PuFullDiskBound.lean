/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.WeightedRadialBound

/-!
# Genus-0 Conformal Disk `2π` Bound from Radial Shell Inradius

This file eliminates the unproved moment assumption in `WeightedRadialBound`
via integration by parts with the increasing weight `w(r) = r * h(r) = 2r / (1 + r²)`:
because `w(0) = 0` and `w'(r) = 2(1 - r²) / (1 + r²)² ≥ 0` on `[0, 1]`, any conformal
disk metric whose angular mean `u(r) = angularMean (lam r)` satisfies the radial shell
inradius bound `π / 2 - 2 * arctan r ≤ ∫ s in r..1, u s` for all `r ∈ [0, 1]`
automatically satisfies `0 ≤ ∫ r in 0..1, r * h r * (u r - h r)` and hence achieves
the sharp conjectured area lower bound `2 * π`.
-/

open MeasureTheory Set

@[expose] public section

noncomputable section

/-- **Lemma 1 (Exact Tail Inradius of the Stereographic Hemisphere):**
For every `r ∈ [0, 1]`, integrating `hemisphereConformalFactor s = 2 / (1 + s ^ 2)`
over `[r, 1]` yields `Real.pi / 2 - 2 * Real.arctan r`. -/
theorem hemisphere_tail_inradius (r : ℝ) :
    (∫ s in r..(1 : ℝ), hemisphereConformalFactor s) =
      Real.pi / 2 - 2 * Real.arctan r := by
  simp only [hemisphereConformalFactor, div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul, integral_inv_one_add_sq, Real.arctan_one]
  ring

/-- **Lemma 2 (Sharp `2π` Area Bound from Radial Shell Distance Lower Bound):**
If `lam : ℝ → ℝ → ℝ` is jointly continuous on `[0, 1] × [0, 2π]` and satisfies
`Real.pi / 2 - 2 * Real.arctan r ≤ ∫ s in r..1, angularMean (lam s)` for every
`r ∈ [0, 1]`, then its total conformal area is at least `2 * Real.pi`. -/
theorem conformal_disk_two_pi_of_tail_inradius (lam : ℝ → ℝ → ℝ)
    (hlam_cont : Continuous (Function.uncurry lam))
    (h_tail : ∀ r ∈ Icc (0 : ℝ) 1,
      Real.pi / 2 - 2 * Real.arctan r ≤ ∫ s in r..(1 : ℝ), angularMean (lam s)) :
    2 * Real.pi ≤
      2 * Real.pi *
        (∫ r in (0 : ℝ)..(1 : ℝ), r * angularMean (fun θ => (lam r θ) ^ 2)) := by
  set h := hemisphereConformalFactor with hh_def
  have hh_cont : Continuous h :=
    continuous_const.div (by fun_prop) (fun r => by positivity)
  have hmean_cont : Continuous (fun r => angularMean (lam r)) :=
    continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hlam_cont _ _)
  set f : ℝ → ℝ := fun r => angularMean (lam r) - h r with hf_def
  have hf_cont : Continuous f := hmean_cont.sub hh_cont
  -- Weight `w r = r * h r` and its derivative.
  set w : ℝ → ℝ := fun r => r * h r with hw_def
  set w' : ℝ → ℝ := fun r => 2 * (1 - r ^ 2) / (1 + r ^ 2) ^ 2 with hw'_def
  have hw_deriv : ∀ r ∈ uIcc (0 : ℝ) 1, HasDerivAt w (w' r) r := by
    intro r _
    have hpos : (1 + r ^ 2) ≠ 0 := by positivity
    have h1 := ((hasDerivAt_id' r).const_mul 2).div
      (((hasDerivAt_id' r).pow 2).const_add 1) hpos
    convert h1 using 1
    · funext x
      simp only [hw_def, hh_def, hemisphereConformalFactor, Pi.div_apply, Pi.pow_apply]
      ring
    · simp only [hw'_def, Pi.pow_apply]
      field_simp
      ring
  have hw'_cont : Continuous w' :=
    (continuous_const.mul (by fun_prop)).div (by fun_prop) (fun r => by positivity)
  -- Tail antiderivative `G r = ∫ s in 1..r, f s = -∫ s in r..1, f s`.
  set G : ℝ → ℝ := fun r => ∫ s in (1 : ℝ)..r, f s with hG_def
  have hG_deriv : ∀ r ∈ uIcc (0 : ℝ) 1, HasDerivAt G (f r) r :=
    fun r _ => (hf_cont.integral_hasStrictDerivAt 1 r).hasDerivAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hw_deriv hG_deriv
    (hw'_cont.intervalIntegrable _ _) (hf_cont.intervalIntegrable _ _)
  have hG1 : G 1 = 0 := by simp [hG_def]
  have hw0 : w 0 = 0 := by simp [hw_def]
  rw [hG1, hw0] at hibp
  -- `-G r` is the tail excess, which is non-negative by `h_tail`.
  have hnegG : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ -G r := by
    intro r hr
    have hsplit : -G r = (∫ s in r..(1 : ℝ), angularMean (lam s)) -
        ∫ s in r..(1 : ℝ), h s := by
      simp only [hG_def]
      rw [intervalIntegral.integral_symm r 1, neg_neg, hf_def,
        intervalIntegral.integral_sub (hmean_cont.intervalIntegrable _ _)
          (hh_cont.intervalIntegrable _ _)]
    rw [hsplit, hh_def, hemisphere_tail_inradius]
    linarith [h_tail r hr]
  have hw'_nonneg : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ w' r := by
    intro r hr
    have : 0 ≤ 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
    simp only [hw'_def]
    positivity
  have h_int_nonneg : 0 ≤ ∫ r in (0 : ℝ)..(1 : ℝ), w' r * -G r :=
    intervalIntegral.integral_nonneg zero_le_one
      (fun r hr => mul_nonneg (hw'_nonneg r hr) (hnegG r hr))
  have h_neg : (∫ r in (0 : ℝ)..(1 : ℝ), w' r * -G r) =
      -∫ r in (0 : ℝ)..(1 : ℝ), w' r * G r := by
    simp only [mul_neg, intervalIntegral.integral_neg]
  have h_moment : 0 ≤ ∫ r in (0 : ℝ)..(1 : ℝ),
      r * hemisphereConformalFactor r *
        (angularMean (lam r) - hemisphereConformalFactor r) := by
    have : (∫ r in (0 : ℝ)..(1 : ℝ), w r * f r) =
        ∫ r in (0 : ℝ)..(1 : ℝ), r * hemisphereConformalFactor r *
          (angularMean (lam r) - hemisphereConformalFactor r) := rfl
    rw [← this, hibp]
    linarith
  exact conformal_disk_area_ge_two_pi_of_moment lam hlam_cont h_moment

end

end

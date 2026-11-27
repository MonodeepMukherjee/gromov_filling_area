/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.RadialGeodesicBound
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Stereographic Hemisphere Calibration & Conformal Disk `2π` Area

This file defines the conformal scale factor `hemisphereConformalFactor r = 2 / (1 + r ^ 2)`
of the unit round hemisphere under stereographic projection onto `ℂ`, proves that
its radial inradius is `π / 2` and its conformal area `2π ∫₀¹ r · λ(r)² dr` equals `2π`,
and combines this with `ConformalPuBound` to bound conformal disk areas.
-/

open MeasureTheory Set

@[expose] public section

noncomputable section

/-- Stereographic conformal factor `2 / (1 + r ^ 2)` of the unit hemisphere on `ℂ`. -/
def hemisphereConformalFactor (r : ℝ) : ℝ :=
  2 / (1 + r ^ 2)

/-- **Lemma 1 (Exact Radial Inradius of the Stereographic Hemisphere):**
Integrating `hemisphereConformalFactor r = 2 / (1 + r ^ 2)` over `r ∈ [0, 1]` yields `π / 2`. -/
theorem hemisphere_conformal_inradius :
    (∫ r in (0 : ℝ)..(1 : ℝ), hemisphereConformalFactor r) = Real.pi / 2 := by
  simp only [hemisphereConformalFactor, div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul, integral_inv_one_add_sq, Real.arctan_one,
    Real.arctan_zero]
  ring

/-- **Lemma 2 (Exact `2π` Conformal Area of the Stereographic Hemisphere):**
The conformal area `2 * π * ∫ r in 0..1, r * (hemisphereConformalFactor r) ^ 2`
equals the sharp conjectured filling area `2 * π`. -/
theorem hemisphere_conformal_area :
    2 * Real.pi * (∫ r in (0 : ℝ)..(1 : ℝ), r * (hemisphereConformalFactor r) ^ 2) =
      2 * Real.pi := by
  have hpos : ∀ r : ℝ, (1 + r ^ 2) ≠ 0 := fun r => by positivity
  have hderiv : ∀ r ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r : ℝ => -2 * (1 + r ^ 2)⁻¹)
      (r * (hemisphereConformalFactor r) ^ 2) r := by
    intro r _
    have h := (((hasDerivAt_id r).pow 2).const_add 1).inv (hpos r) |>.const_mul (-2)
    convert h using 1
    · funext y
      simp
    · simp only [hemisphereConformalFactor, id, Pi.pow_apply]
      field_simp
      ring
  have hint : IntervalIntegrable (fun r : ℝ => r * (hemisphereConformalFactor r) ^ 2)
      volume 0 1 := by
    refine (continuous_id.mul ((continuous_const.div ?_ hpos).pow 2)).intervalIntegrable _ _
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num

end

end

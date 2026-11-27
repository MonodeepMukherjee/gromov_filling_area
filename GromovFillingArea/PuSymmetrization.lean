/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.UniversalAreaBound
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Pu's Rotational Symmetrization & Sharp `2π` Hemisphere Area Bound

This file formalizes the core analytic step of Pu's theorem (the genus-`0` case of
Gromov's Filling Area Conjecture): for a rotationally symmetric Riemannian disk
`ds² = dr² + φ(r)² dθ²` whose radial circumference profile satisfies the isometric
no-shortcut lower bound `Real.sin t ≤ φ t` on `[0, π / 2]`, the surface area
`2 * π * ∫ t in 0..(π / 2), φ t` is at least the sharp hemisphere area `2 * π`.
-/

open MeasureTheory Set

@[expose] public section

noncomputable section

/-- **Lemma 1 (Exact Area of the Round Hemisphere):**
Integrating the radial circumference `2 * π * sin t` over `t ∈ [0, π / 2]`
gives the exact sharp filling area `2 * π`. -/
theorem hemisphere_radial_area :
    2 * Real.pi * (∫ t in (0 : ℝ)..(Real.pi / 2), Real.sin t) = 2 * Real.pi := by
  rw [integral_sin, Real.cos_zero, Real.cos_pi_div_two, sub_zero, mul_one]

/-- **Lemma 2 (Sharp `2π` Lower Bound for Rotationally Symmetric Fillings):**
If a continuous radial profile `φ : ℝ → ℝ` satisfies `Real.sin t ≤ φ t` for all
`t ∈ [0, π / 2]`, then its annular area `2 * π * ∫ t in 0..(π / 2), φ t` is at
least `2 * π`. -/
theorem pu_symmetric_filling_area_ge_two_pi (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (hφ_bound : ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2), Real.sin t ≤ φ t) :
    2 * Real.pi ≤ 2 * Real.pi * (∫ t in (0 : ℝ)..(Real.pi / 2), φ t) := by
  have h_mono : (∫ t in (0 : ℝ)..(Real.pi / 2), Real.sin t) ≤
      ∫ t in (0 : ℝ)..(Real.pi / 2), φ t :=
    intervalIntegral.integral_mono_on (by positivity) (Real.continuous_sin.intervalIntegrable _ _)
      (hφ_cont.intervalIntegrable _ _) hφ_bound
  calc 2 * Real.pi
      = 2 * Real.pi * (∫ t in (0 : ℝ)..(Real.pi / 2), Real.sin t) :=
        hemisphere_radial_area.symm
    _ ≤ 2 * Real.pi * (∫ t in (0 : ℝ)..(Real.pi / 2), φ t) :=
        mul_le_mul_of_nonneg_left h_mono Real.two_pi_pos.le

end

end

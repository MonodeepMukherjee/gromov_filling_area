/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.ConformalPuBound

/-!
# Antipodal Diameter & Symmetrized Radial Length Bound

This file proves that if a conformal disk metric `λ(r, θ)² (dr² + r² dθ²)`
satisfies the antipodal diameter condition `π ≤ ∫₀¹ λ(r, θ) dr + ∫₀¹ λ(r, θ + π) dr`
for all angles `θ` (where `λ(r, ·)` is `2π`-periodic), then the rotationally
symmetrized radial radius `∫₀¹ angularMean (λ r) dr` is at least `π / 2`.
-/

open MeasureTheory Set

@[expose] public section

noncomputable section

/-- Radial geodesic length `∫ r in 0..1, lam r θ` along the ray at angle `θ`. -/
def radialRayLength (lam : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..(1 : ℝ), lam r θ

/-- **Lemma 1 (Average Antipodal Radial Length Lower Bound):**
If `L : ℝ → ℝ` is continuous and `2π`-periodic and satisfies `π ≤ L θ + L (θ + π)`
for all `θ`, then `(2 * π)⁻¹ * ∫ θ in 0..(2 * π), L θ ≥ π / 2`. -/
theorem angularMean_ge_half_pi_of_antipodal_sum (L : ℝ → ℝ)
    (hL_cont : Continuous L) (hL_per : Function.Periodic L (2 * Real.pi))
    (hL_anti : ∀ θ : ℝ, Real.pi ≤ L θ + L (θ + Real.pi)) :
    Real.pi / 2 ≤ angularMean L := by
  have hL_int : ∀ a b : ℝ, IntervalIntegrable L volume a b := fun a b =>
    hL_cont.intervalIntegrable a b
  have hg : IntervalIntegrable (fun θ => L (θ + Real.pi)) volume 0 Real.pi :=
    (hL_cont.comp (continuous_id.add continuous_const)).intervalIntegrable 0 Real.pi
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hL_int 0 Real.pi)
    (hL_int Real.pi (2 * Real.pi))
  have hshift : (∫ θ in (0 : ℝ)..Real.pi, L (θ + Real.pi)) =
      ∫ θ in Real.pi..(2 * Real.pi), L θ := by
    rw [intervalIntegral.integral_comp_add_right L Real.pi, zero_add, ← two_mul]
  have hadd := intervalIntegral.integral_add (hL_int 0 Real.pi) hg
  have hmono := intervalIntegral.integral_mono_on Real.pi_pos.le
    (intervalIntegrable_const (c := Real.pi)) ((hL_int 0 Real.pi).add hg)
    (fun θ _ => hL_anti θ)
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
  have htot : Real.pi * Real.pi ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), L θ := by
    linarith
  have hL : 0 < 2 * Real.pi := Real.two_pi_pos
  rw [angularMean, le_inv_mul_iff₀ hL]
  nlinarith

/-- **Lemma 2 (Symmetrized Conformal Disk Inradius Bound):**
If `lam : ℝ → ℝ → ℝ` is jointly continuous, `2π`-periodic in `θ`, and satisfies
`π ≤ radialRayLength lam θ + radialRayLength lam (θ + π)` for all `θ`, then
the symmetrized radial radius `∫ r in 0..1, angularMean (lam r)` is at least `π / 2`. -/
theorem symmetrized_radial_radius_ge_half_pi (lam : ℝ → ℝ → ℝ)
    (hlam_cont : Continuous (Function.uncurry lam))
    (hlam_per : ∀ r θ : ℝ, lam r (θ + 2 * Real.pi) = lam r θ)
    (hlam_anti : ∀ θ : ℝ, Real.pi ≤ radialRayLength lam θ + radialRayLength lam (θ + Real.pi)) :
    Real.pi / 2 ≤ ∫ r in (0 : ℝ)..(1 : ℝ), angularMean (lam r) := by
  have h_on : IntegrableOn (Function.uncurry lam)
      (uIoc (0 : ℝ) 1 ×ˢ uIoc (0 : ℝ) (2 * Real.pi)) :=
    (hlam_cont.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have h_swap : (∫ r in (0 : ℝ)..(1 : ℝ), angularMean (lam r)) =
      angularMean (radialRayLength lam) := by
    simp only [angularMean, radialRayLength, intervalIntegral.integral_const_mul]
    rw [intervalIntegral_intervalIntegral_swap h_on]
  have h_cont : Continuous (radialRayLength lam) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun θ r => lam r θ) (hlam_cont.comp continuous_swap) 0 1
  have h_per : Function.Periodic (radialRayLength lam) (2 * Real.pi) := fun θ => by
    simp only [radialRayLength, hlam_per]
  rw [h_swap]
  exact angularMean_ge_half_pi_of_antipodal_sum _ h_cont h_per hlam_anti

end

end

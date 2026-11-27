/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.PuSymmetrization
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Conformal Rotational Symmetrization & Cauchy–Schwarz Area Decrease

This file formalizes the angular averaging step of Pu's symmetrization for
conformal metrics `ds² = λ(r, θ)² (dr² + r² dθ²)` on the unit disk: proving via
Cauchy–Schwarz on `[0, 2π]` that the rotationally averaged scale factor
`λ̄(r) = (2π)⁻¹ ∫₀^{2π} λ(r, θ) dθ` satisfies `λ̄(r)² ≤ (2π)⁻¹ ∫₀^{2π} λ(r, θ)² dθ`,
so rotational symmetrization never increases Riemannian surface area.
-/

open MeasureTheory Set

@[expose] public section

noncomputable section

/-- Angular average `(2 * π)⁻¹ * ∫ θ in 0..(2 * π), f θ` of a periodic conformal factor. -/
def angularMean (f : ℝ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ)

/-- **Lemma 1 (Cauchy–Schwarz Angular Squaring Inequality):**
For any continuous conformal scale factor `f : ℝ → ℝ` on `[0, 2π]`, the square of
its angular mean is at most the angular mean of `f ^ 2`:
`(angularMean f) ^ 2 ≤ angularMean (fun θ => f θ ^ 2)`. -/
theorem angularMean_sq_le (f : ℝ → ℝ) (hf : Continuous f) :
    (angularMean f) ^ 2 ≤ angularMean (fun θ => f θ ^ 2) := by
  set c := angularMean f with hc
  have hL : 0 < 2 * Real.pi := Real.two_pi_pos
  have hf_int : IntervalIntegrable f volume 0 (2 * Real.pi) := hf.intervalIntegrable _ _
  have hf2_int : IntervalIntegrable (fun θ => f θ ^ 2) volume 0 (2 * Real.pi) :=
    (hf.pow 2).intervalIntegrable _ _
  have h0 : 0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), (f θ - c) ^ 2 :=
    intervalIntegral.integral_nonneg hL.le (fun _ _ => sq_nonneg _)
  have hexp : (∫ θ in (0 : ℝ)..(2 * Real.pi), (f θ - c) ^ 2) =
      (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ ^ 2)
        - 2 * c * (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ) + 2 * Real.pi * c ^ 2 := by
    have hfun : (fun θ => (f θ - c) ^ 2) = fun θ => (f θ ^ 2 - (2 * c) * f θ) + c ^ 2 := by
      funext θ; ring
    rw [hfun, intervalIntegral.integral_add (hf2_int.sub (hf_int.const_mul _))
      intervalIntegrable_const, intervalIntegral.integral_sub hf2_int (hf_int.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
  have hI : (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ) = 2 * Real.pi * c := by
    rw [hc, angularMean, ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
  change c ^ 2 ≤ (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ ^ 2)
  rw [le_inv_mul_iff₀ hL]
  rw [hexp, hI] at h0
  nlinarith

/-- **Lemma 2 (Radial Area Contraction Under Rotational Symmetrization):**
For any non-negative radial weight `w : ℝ → ℝ` (`0 ≤ w r` on `[0, 1]`) and
continuous `λ : ℝ → ℝ → ℝ`, integrating `w r * (angularMean (λ r)) ^ 2` over
`r ∈ [0, 1]` is at most `∫ r in 0..1, w r * angularMean (fun θ => (λ r θ) ^ 2)`. -/
theorem radial_symmetrized_area_le (w : ℝ → ℝ) (hw_cont : Continuous w)
    (hw_nonneg : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ w r)
    (lam : ℝ → ℝ → ℝ) (hlam_cont : ∀ r, Continuous (lam r))
    (h_int_cont : Continuous (fun r => w r * angularMean (fun θ => (lam r θ) ^ 2))) :
    (∫ r in (0 : ℝ)..(1 : ℝ), w r * (angularMean (lam r)) ^ 2) ≤
      (∫ r in (0 : ℝ)..(1 : ℝ), w r * angularMean (fun θ => (lam r θ) ^ 2)) := by
  have h_pt : ∀ r ∈ Icc (0 : ℝ) 1,
      w r * (angularMean (lam r)) ^ 2 ≤ w r * angularMean (fun θ => (lam r θ) ^ 2) :=
    fun r hr => mul_le_mul_of_nonneg_left (angularMean_sq_le _ (hlam_cont r)) (hw_nonneg r hr)
  by_cases h_int : IntervalIntegrable (fun r => w r * (angularMean (lam r)) ^ 2) volume 0 1
  · exact intervalIntegral.integral_mono_on zero_le_one h_int
      (h_int_cont.intervalIntegrable _ _) h_pt
  · rw [intervalIntegral.integral_undef h_int]
    exact intervalIntegral.integral_nonneg zero_le_one
      (fun r hr => (mul_nonneg (hw_nonneg r hr) (sq_nonneg _)).trans (h_pt r hr))

end

end

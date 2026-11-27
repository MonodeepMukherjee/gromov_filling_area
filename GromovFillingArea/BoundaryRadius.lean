/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.BoundaryCircleImage
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact Boundary Circle Radii for Odd Fourier Modes

This file evaluates the base boundary profile `t ↦ kuratowskiMap F (F.ι 0) (t : Circle2Pi)`
on `[0, 2π]` as the tent function `min t (2π - t)`, and computes the exact radius
`‖fourierProj (2 * k + 1) (kuratowskiBanach F (F.ι 0))‖ = 2 / ((2 * k + 1 : ℝ) ^ 2 * π)`
of the projected boundary circle in `ℂ`.
-/

open MeasureTheory Metric Set BoundedContinuousFunction AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Lemma 1 (Tent Function Reduction on `[0, 2π]`):**
For `t ∈ [0, 2π]`, the base boundary profile `kuratowskiMap F (F.ι 0) (t : Circle2Pi)`
equals `min t (2 * Real.pi - t)`. -/
theorem kuratowskiMap_boundary_zero_eq_min (F : IsometricFilling M)
    {t : ℝ} (ht0 : 0 ≤ t) (ht2pi : t ≤ 2 * Real.pi) :
    kuratowskiMap F (F.ι 0) (t : Circle2Pi) = min t (2 * Real.pi - t) := by
  rw [kuratowskiMap_boundary, dist_zero_left]
  rcases le_or_gt t Real.pi with h | h
  · rw [circle2Pi_norm_coe_of_abs_le t (by rw [abs_of_nonneg ht0]; exact h),
      abs_of_nonneg ht0, min_eq_left (by linarith)]
  · have hshift : (t : Circle2Pi) = ((t - 2 * Real.pi : ℝ) : Circle2Pi) := by
      rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
    rw [hshift, circle2Pi_norm_coe_of_abs_le (t - 2 * Real.pi)
        (by rw [abs_of_nonpos (by linarith)]; linarith),
      abs_of_nonpos (by linarith), min_eq_right (by linarith)]
    ring

/-- On real points, the `(-n)`-th character is `x ↦ exp (-n * I * x)`. -/
theorem fourier_neg_coe_eq_cexp (n : ℤ) (x : ℝ) :
    fourier (-n) (x : Circle2Pi) = Complex.exp (-(n : ℂ) * Complex.I * x) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

/-- Antiderivative formula: `∫ exp (c x) (p + q x) dx` for `c ≠ 0`. -/
theorem integral_cexp_mul_affine (c p q : ℂ) (hc : c ≠ 0) (u v : ℝ) :
    ∫ x in u..v, Complex.exp (c * x) * (p + q * x) =
      Complex.exp (c * v) * ((p + q * v) / c - q / c ^ 2) -
        Complex.exp (c * u) * ((p + q * u) / c - q / c ^ 2) := by
  have hcont : Continuous (fun x : ℝ => Complex.exp (c * x) * (p + q * x)) := by
    fun_prop
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => Complex.exp (c * x) * ((p + q * x) / c - q / c ^ 2)) (fun x _ => ?_)
    (hcont.intervalIntegrable u v)
  have hx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
  have he := (hx.const_mul c).cexp
  have hl := ((hx.const_mul q).const_add p).div_const c |>.sub_const (q / c ^ 2)
  convert he.mul hl using 1
  field_simp
  ring

/-- For odd `n = 2k + 1`, `exp (-n * I * π) = -1`. -/
theorem cexp_odd_mul_pi (k : ℕ) :
    Complex.exp (-(((2 * (k : ℤ) + 1 : ℤ)) : ℂ) * Complex.I * (Real.pi : ℝ)) = -1 := by
  have h : -(((2 * (k : ℤ) + 1 : ℤ)) : ℂ) * Complex.I * (Real.pi : ℝ) =
      ((-(2 * (k : ℤ) + 1) : ℤ) : ℂ) * (Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul, Complex.exp_pi_mul_I, (odd_two_mul_add_one (k : ℤ)).neg.neg_one_zpow]

/-- For every integer `n`, `exp (-n * I * 2π) = 1`. -/
theorem cexp_int_mul_two_pi (n : ℤ) :
    Complex.exp (-(n : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
  have h : -(n : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ) =
      ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- The real-variable integrand of the base boundary coefficient is continuous. -/
theorem boundary_integrand_continuous (F : IsometricFilling M) (n : ℤ) :
    Continuous (fun x : ℝ =>
      fourier (-n) (x : Circle2Pi) • ((kuratowskiBanach F (F.ι 0)) (x : Circle2Pi) : ℂ)) :=
  ((fourier (-n)).continuous.comp circle2Pi_coe_lipschitz.continuous).smul
    ((Complex.continuous_ofReal.comp (kuratowskiBanach F (F.ι 0)).continuous).comp
      circle2Pi_coe_lipschitz.continuous)

/-- The unnormalized odd-mode integral of the base boundary profile equals `-4 / n²`. -/
theorem boundary_odd_integral (F : IsometricFilling M) (k : ℕ) :
    ∫ x in (0 : ℝ)..(2 * Real.pi),
      fourier (-(2 * (k : ℤ) + 1)) (x : Circle2Pi) •
        ((kuratowskiBanach F (F.ι 0)) (x : Circle2Pi) : ℂ) =
      -4 / (((2 * (k : ℤ) + 1 : ℤ)) : ℂ) ^ 2 := by
  have hπ := Real.pi_pos
  have hn : (((2 * (k : ℤ) + 1 : ℤ)) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
  have hc : -(((2 * (k : ℤ) + 1 : ℤ)) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hn) Complex.I_ne_zero
  have hg := boundary_integrand_continuous F (2 * (k : ℤ) + 1)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable 0 Real.pi)
    (hg.intervalIntegrable Real.pi (2 * Real.pi))]
  have h1 : ∫ x in (0 : ℝ)..Real.pi,
        fourier (-(2 * (k : ℤ) + 1)) (x : Circle2Pi) •
          ((kuratowskiBanach F (F.ι 0)) (x : Circle2Pi) : ℂ) =
      ∫ x in (0 : ℝ)..Real.pi, Complex.exp (-(((2 * (k : ℤ) + 1 : ℤ)) : ℂ) * Complex.I * x) *
        (0 + 1 * x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hπ.le] at hx
    rw [fourier_neg_coe_eq_cexp, kuratowskiBanach_apply,
      kuratowskiMap_boundary_zero_eq_min F hx.1 (by linarith [hx.2]),
      min_eq_left (by linarith [hx.2]), smul_eq_mul]
    ring
  have h2 : ∫ x in Real.pi..(2 * Real.pi),
        fourier (-(2 * (k : ℤ) + 1)) (x : Circle2Pi) •
          ((kuratowskiBanach F (F.ι 0)) (x : Circle2Pi) : ℂ) =
      ∫ x in Real.pi..(2 * Real.pi),
        Complex.exp (-(((2 * (k : ℤ) + 1 : ℤ)) : ℂ) * Complex.I * x) *
          ((2 * Real.pi : ℝ) + (-1) * x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    rw [fourier_neg_coe_eq_cexp, kuratowskiBanach_apply,
      kuratowskiMap_boundary_zero_eq_min F (by linarith [hx.1]) hx.2,
      min_eq_right (by linarith [hx.1]), smul_eq_mul]
    push_cast
    ring
  rw [h1, h2, integral_cexp_mul_affine _ _ _ hc, integral_cexp_mul_affine _ _ _ hc,
    cexp_int_mul_two_pi, cexp_odd_mul_pi]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  field_simp
  push_cast
  linear_combination 4 * hI

/-- **Lemma 2 (Explicit Odd-Mode Boundary Radius in `ℂ`):**
For every `k : ℕ`, the `(2 * k + 1)`-th Fourier projection of `F.ι 0` has exact
norm `2 / ((2 * (k : ℝ) + 1) ^ 2 * Real.pi)`. -/
theorem fourierProj_boundary_odd_norm (F : IsometricFilling M) (k : ℕ) :
    ‖fourierProj (2 * (k : ℤ) + 1) (kuratowskiBanach F (F.ι 0))‖ =
      2 / ((2 * (k : ℝ) + 1) ^ 2 * Real.pi) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hk : (2 * (k : ℂ) + 1) ≠ 0 := by
    norm_cast
  rw [fourierProj, fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [zero_add]
  rw [boundary_odd_integral]
  have hval : (1 / (2 * Real.pi)) • (-4 / (((2 * (k : ℤ) + 1 : ℤ)) : ℂ) ^ 2) =
      ((-(2 / ((2 * (k : ℝ) + 1) ^ 2 * Real.pi)) : ℝ) : ℂ) := by
    rw [Complex.real_smul]
    push_cast
    field_simp
    norm_num
  rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]

end

end

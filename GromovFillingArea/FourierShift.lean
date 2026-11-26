/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.OddHarmonics

/-!
# Fourier Half-Period Shift & Vanishing of Even Harmonics

This file proves that shifting a function on `Circle2Pi` by `π` multiplies its
`n`-th Fourier coefficient by `(-1 : ℂ) ^ n`, implying that all even-indexed
Fourier coefficients `fourierCoeff (antipodalDiff F x) (2 * k)` vanish.
-/

open MeasureTheory Metric AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- `fourier n` is a character: `e_n(a + b) = e_n(a) * e_n(b)` on `Circle2Pi`. -/
theorem fourier_add_arg (n : ℤ) (a b : Circle2Pi) :
    fourier n (a + b) = fourier n a * fourier n b := by
  simp only [fourier_apply, zsmul_add, toCircle_add, Circle.coe_mul]

/-- Evaluating the `(-n)`-th character at the half-period `-π` gives `(-1) ^ n`. -/
theorem fourier_neg_index_neg_pi (n : ℤ) :
    fourier (-n) (-(Real.pi : Circle2Pi)) = (-1 : ℂ) ^ n := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← AddCircle.coe_neg, fourier_coe_apply]
  have harg : 2 * (Real.pi : ℂ) * Complex.I * ((-n : ℤ) : ℂ) * ((-Real.pi : ℝ) : ℂ) /
      ((2 * Real.pi : ℝ) : ℂ) = (n : ℂ) * (Real.pi * Complex.I) := by
    push_cast
    field_simp
  rw [harg, Complex.exp_int_mul, Complex.exp_pi_mul_I]

/-- Fourier coefficients commute with pointwise negation. -/
theorem fourierCoeff_neg_fun (g : Circle2Pi → ℂ) (n : ℤ) :
    fourierCoeff (fun θ => -g θ) n = -fourierCoeff g n := by
  simp only [fourierCoeff, smul_neg, integral_neg]

/-- **Lemma 1 (Half-Period Shift on `fourierCoeff`):**
Translating `g : Circle2Pi → ℂ` by `π` scales `fourierCoeff g n` by `(-1 : ℂ) ^ n`. -/
theorem fourierCoeff_add_pi (g : Circle2Pi → ℂ) (n : ℤ) :
    fourierCoeff (fun θ : Circle2Pi => g (θ + (Real.pi : Circle2Pi))) n =
      (-1 : ℂ) ^ n * fourierCoeff g n := by
  have hchar : ∀ t : Circle2Pi, fourier (-n) t =
      fourier (-n) (t + (Real.pi : Circle2Pi)) * fourier (-n) (-(Real.pi : Circle2Pi)) := by
    intro t
    rw [← fourier_add_arg, add_neg_cancel_right]
  have hfun : (fun t : Circle2Pi => fourier (-n) t • g (t + (Real.pi : Circle2Pi))) =
      fun t => fourier (-n) (-(Real.pi : Circle2Pi)) •
        (fun s : Circle2Pi => fourier (-n) s • g s) (t + (Real.pi : Circle2Pi)) := by
    funext t
    simp only [smul_eq_mul]
    rw [hchar t]
    ring
  simp only [fourierCoeff]
  rw [hfun, integral_smul,
    integral_add_right_eq_self (fun s : Circle2Pi => fourier (-n) s • g s),
    fourier_neg_index_neg_pi, smul_eq_mul]

/-- **Lemma 2 (Vanishing of Even Fourier Modes of `antipodalDiff`):**
For every integer `k : ℤ`, the `(2 * k)`-th Fourier coefficient of
`antipodalDiff F x` is `0`. -/
theorem antipodalDiff_fourierCoeff_even (F : IsometricFilling M) (x : M) (k : ℤ) :
    fourierCoeff (antipodalDiff F x) (2 * k) = 0 := by
  have h := fourierCoeff_add_pi (antipodalDiff F x) (2 * k)
  have hfun : (fun θ : Circle2Pi => antipodalDiff F x (θ + (Real.pi : Circle2Pi))) =
      fun θ => -antipodalDiff F x θ := funext (antipodalDiff_add_pi F x)
  rw [hfun, fourierCoeff_neg_fun, (even_two_mul k).neg_one_zpow, one_mul] at h
  linear_combination (-1 / 2 : ℂ) * h

end

end

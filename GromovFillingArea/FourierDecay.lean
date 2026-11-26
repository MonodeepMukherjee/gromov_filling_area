/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.OddLowerBound

/-!
# High-Frequency Fourier Coefficient Decay for Lipschitz Profiles

This file proves the `O(1 / |n|)` spectral decay bound for 1-Lipschitz profiles
on `Circle2Pi` via the half-wavelength shift `θ ↦ θ + π / n`, avoiding weak
derivatives while establishing `‖f̂_x(n)‖ ≤ π / (2 * |(n : ℝ)|)` for `n ≠ 0`.
-/

open MeasureTheory Metric AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Shifting `g` by `s` multiplies `fourierCoeff g n` by the character value `e_{-n}(-s)`. -/
theorem fourierCoeff_add_shift (g : Circle2Pi → ℂ) (n : ℤ) (s : ℝ) :
    fourierCoeff (fun θ : Circle2Pi => g (θ + (s : Circle2Pi))) n =
      fourier (-n) (-(s : Circle2Pi)) * fourierCoeff g n := by
  have hchar : ∀ t : Circle2Pi, fourier (-n) t =
      fourier (-n) (t + (s : Circle2Pi)) * fourier (-n) (-(s : Circle2Pi)) := by
    intro t
    rw [← fourier_add_arg, add_neg_cancel_right]
  have hfun : (fun t : Circle2Pi => fourier (-n) t • g (t + (s : Circle2Pi))) =
      fun t => fourier (-n) (-(s : Circle2Pi)) •
        (fun u : Circle2Pi => fourier (-n) u • g u) (t + (s : Circle2Pi)) := by
    funext t
    simp only [smul_eq_mul]
    rw [hchar t]
    ring
  simp only [fourierCoeff]
  rw [hfun, integral_smul, integral_add_right_eq_self (fun u : Circle2Pi => fourier (-n) u • g u),
    smul_eq_mul]

/-- At the half-wavelength `π / n`, the `(-n)`-th character takes the value `-1`. -/
theorem fourier_neg_index_neg_pi_div (n : ℤ) (hn : n ≠ 0) :
    fourier (-n) (-((Real.pi / n : ℝ) : Circle2Pi)) = -1 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  rw [← AddCircle.coe_neg, fourier_coe_apply]
  have harg : 2 * (Real.pi : ℂ) * Complex.I * ((-n : ℤ) : ℂ) * ((-(Real.pi / n) : ℝ) : ℂ) /
      ((2 * Real.pi : ℝ) : ℂ) = Real.pi * Complex.I := by
    push_cast
    field_simp
  rw [harg, Complex.exp_pi_mul_I]

/-- A pointwise bound `‖g θ‖ ≤ C` bounds every Fourier coefficient by `C`. -/
theorem fourierCoeff_norm_le_of_norm_le (g : Circle2Pi → ℂ) (C : ℝ) (hC : ∀ θ, ‖g θ‖ ≤ C)
    (n : ℤ) : ‖fourierCoeff g n‖ ≤ C := by
  have h : ∀ᵐ t ∂(haarAddCircle : Measure Circle2Pi), ‖fourier (-n) t • g t‖ ≤ C := by
    refine Filter.Eventually.of_forall fun t => ?_
    rw [norm_smul]
    calc ‖fourier (-n) t‖ * ‖g t‖ ≤ 1 * C :=
          mul_le_mul (fourier_apply_norm_le_one (-n) t) (hC t) (norm_nonneg _) zero_le_one
      _ = C := one_mul _
  have hI := norm_integral_le_of_norm_le_const h
  rw [probReal_univ, mul_one] at hI
  rw [fourierCoeff]
  exact hI

/-- **Lemma 1 (Half-Wavelength Shift Identity on `fourierCoeff`):**
For any `n ≠ 0` and continuous `g : Circle2Pi → ℂ`, shifting by `π / n` negates
`fourierCoeff g n`, so `2 * fourierCoeff g n` equals the `n`-th coefficient of
`θ ↦ g θ - g (θ + (Real.pi / n : Circle2Pi))`. -/
theorem two_mul_fourierCoeff_eq_sub_shift (g : Circle2Pi → ℂ) (hg : Continuous g)
    (n : ℤ) (hn : n ≠ 0) :
    2 * fourierCoeff g n =
      fourierCoeff (fun θ : Circle2Pi => g θ - g (θ + ((Real.pi / n : ℝ) : Circle2Pi))) n := by
  have hshift : Continuous (fun θ : Circle2Pi => g (θ + ((Real.pi / n : ℝ) : Circle2Pi))) :=
    hg.comp (continuous_id.add continuous_const)
  rw [fourierCoeff_sub_of_continuous _ _ hg hshift, fourierCoeff_add_shift,
    fourier_neg_index_neg_pi_div n hn]
  ring

/-- The half-wavelength difference of the Kuratowski profile is bounded by `π / |n|`. -/
theorem kuratowskiComplex_shift_diff_norm_le (F : IsometricFilling M) (x : M) (n : ℤ)
    (θ : Circle2Pi) :
    ‖kuratowskiComplex F x θ - kuratowskiComplex F x (θ + ((Real.pi / n : ℝ) : Circle2Pi))‖ ≤
      Real.pi / |(n : ℝ)| := by
  rw [kuratowskiComplex, kuratowskiComplex, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  calc _ ≤ dist θ (θ + ((Real.pi / n : ℝ) : Circle2Pi)) := kuratowski_lipschitz F x θ _
    _ = ‖((Real.pi / n : ℝ) : Circle2Pi)‖ := by rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
    _ ≤ ‖(Real.pi / n : ℝ)‖ := QuotientAddGroup.norm_mk_le_norm
    _ = Real.pi / |(n : ℝ)| := by rw [Real.norm_eq_abs, abs_div, abs_of_pos Real.pi_pos]

/-- **Lemma 2 (High-Frequency Fourier Decay for Kuratowski Profiles):**
For every non-zero frequency `n : ℤ`, `‖fourierCoeff (kuratowskiComplex F x) n‖`
is bounded above by `π / (2 * |(n : ℝ)|)`. -/
theorem kuratowski_fourierCoeff_decay (F : IsometricFilling M) (x : M) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeff (kuratowskiComplex F x) n‖ ≤ Real.pi / (2 * |(n : ℝ)|) := by
  have hb := fourierCoeff_norm_le_of_norm_le _ _ (kuratowskiComplex_shift_diff_norm_le F x n) n
  rw [← two_mul_fourierCoeff_eq_sub_shift _ (kuratowskiComplex_continuous F x) n hn, norm_mul,
    Complex.norm_two] at hb
  have hsplit : Real.pi / (2 * |(n : ℝ)|) = Real.pi / |(n : ℝ)| / 2 := by ring
  rw [hsplit]
  linarith

end

end

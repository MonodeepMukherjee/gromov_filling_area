/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.OddEnergy

/-!
# Uniform Amplitude & Odd-Harmonic Coefficient Bounds

This file proves the sharp pointwise bound `‖antipodalDiff F x θ‖ ≤ π` from
antipodal diameter `dist θ (θ + π) = π`, and deduces the uniform spectral bound
`‖fourierCoeff (kuratowskiComplex F x) (2 * k + 1)‖ ≤ π / 2` on every odd mode.
-/

open MeasureTheory Metric AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Lemma 1 (Pointwise Antipodal Difference Bound):**
For every `x : M` and `θ : Circle2Pi`, `‖antipodalDiff F x θ‖ ≤ π`. -/
theorem antipodalDiff_norm_le_pi (F : IsometricFilling M) (x : M) (θ : Circle2Pi) :
    ‖antipodalDiff F x θ‖ ≤ Real.pi := by
  rw [antipodalDiff, kuratowskiComplex, kuratowskiComplex, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  exact (kuratowski_lipschitz F x θ _).trans (circle2Pi_dist_add_pi θ).le

/-- Every character `fourier n` on `Circle2Pi` has pointwise norm at most `1`. -/
theorem fourier_apply_norm_le_one (n : ℤ) (t : Circle2Pi) : ‖fourier n t‖ ≤ 1 := by
  have h := (fourier (T := 2 * Real.pi) n).norm_coe_le_norm t
  rwa [fourier_norm] at h

/-- Every Fourier coefficient of `antipodalDiff F x` has norm at most `π`
(the Haar measure is a probability measure). -/
theorem antipodalDiff_fourierCoeff_norm_le (F : IsometricFilling M) (x : M) (n : ℤ) :
    ‖fourierCoeff (antipodalDiff F x) n‖ ≤ Real.pi := by
  have h : ∀ᵐ t ∂(haarAddCircle : Measure Circle2Pi),
      ‖fourier (-n) t • antipodalDiff F x t‖ ≤ Real.pi := by
    refine Filter.Eventually.of_forall fun t => ?_
    rw [norm_smul]
    calc ‖fourier (-n) t‖ * ‖antipodalDiff F x t‖ ≤ 1 * Real.pi :=
          mul_le_mul (fourier_apply_norm_le_one (-n) t) (antipodalDiff_norm_le_pi F x t)
            (norm_nonneg _) zero_le_one
      _ = Real.pi := one_mul _
  have hI := norm_integral_le_of_norm_le_const h
  rw [probReal_univ, mul_one] at hI
  rw [fourierCoeff]
  exact hI

/-- **Lemma 2 (Uniform Odd Fourier Coefficient Bound):**
Every odd Fourier coefficient `fourierCoeff (kuratowskiComplex F x) (2 * k + 1)`
has norm at most `π / 2`. -/
theorem kuratowski_odd_fourierCoeff_norm_le (F : IsometricFilling M) (x : M) (k : ℤ) :
    ‖fourierCoeff (kuratowskiComplex F x) (2 * k + 1)‖ ≤ Real.pi / 2 := by
  have h := antipodalDiff_fourierCoeff_norm_le F x (2 * k + 1)
  rw [antipodalDiff_fourierCoeff_odd, norm_mul, Complex.norm_two] at h
  linarith

end

end

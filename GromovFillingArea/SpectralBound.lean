/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.ParsevalEnergy

/-!
# Spectral Fourier Energy Lower Bound

This file relates the normalized Haar integral on `Circle2Pi` to the interval
integral on `[0, 2π]` via `AddCircle.integral_preimage` and deduces the
spectral energy bound
`π ^ 2 / 4 ≤ ∑' n : ℤ, ‖fourierCoeff (kuratowskiComplex F x) n‖ ^ 2`.
-/

open MeasureTheory Metric AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The squared norm of the complexified profile is the squared real profile. -/
theorem kuratowskiComplex_norm_sq (F : IsometricFilling M) (x : M) (θ : Circle2Pi) :
    ‖kuratowskiComplex F x θ‖ ^ 2 = kuratowskiMap F x θ ^ 2 := by
  rw [kuratowskiComplex, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The normalized Haar `L²` energy is `(2π)⁻¹` times the interval energy on `[0, 2π]`. -/
theorem kuratowski_haar_integral_eq (F : IsometricFilling M) (x : M) :
    ∫ θ : Circle2Pi, ‖kuratowskiComplex F x θ‖ ^ 2 ∂haarAddCircle =
      (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi), (periodicDistance F x t) ^ 2 := by
  rw [integral_haarAddCircle, smul_eq_mul,
    ← AddCircle.intervalIntegral_preimage (2 * Real.pi) 0]
  simp only [zero_add, kuratowskiComplex_norm_sq, periodicDistance]

/-- **Lemma 1 (Normalized Haar L² Lower Bound):**
Under the normalized Haar measure `haarAddCircle` on `Circle2Pi`, the average
squared boundary distance from any `x : M` is at least `π ^ 2 / 4`. -/
theorem kuratowski_haar_l2_lower_bound (F : IsometricFilling M) (x : M) :
    Real.pi ^ 2 / 4 ≤
      ∫ θ : Circle2Pi, ‖kuratowskiComplex F x θ‖ ^ 2 ∂haarAddCircle := by
  rw [kuratowski_haar_integral_eq]
  have h := periodicDistance_l2_lower_bound F x
  have hpos : 0 ≤ (2 * Real.pi)⁻¹ := (inv_pos.mpr Real.two_pi_pos).le
  calc Real.pi ^ 2 / 4 = (2 * Real.pi)⁻¹ * (Real.pi ^ 3 / 2) := by
        field_simp
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h hpos

/-- **Lemma 2 (Fourier Coefficient Spectral Energy Bound):**
The sum of squared Fourier coefficients of `kuratowskiComplex F x` is at least
`π ^ 2 / 4`. -/
theorem kuratowski_fourier_energy_lower_bound (F : IsometricFilling M) (x : M) :
    Real.pi ^ 2 / 4 ≤ ∑' n : ℤ, ‖fourierCoeff (kuratowskiComplex F x) n‖ ^ 2 := by
  rw [(kuratowski_parseval_hasSum F x).tsum_eq]
  exact kuratowski_haar_l2_lower_bound F x

end

end

/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.FourierDecay

/-!
# Odd-Harmonic Inverse-Cube Spectral Bound

This file specializes `kuratowski_fourierCoeff_decay` to odd frequencies `2 * k + 1`
(`‖f̂_x(2k+1)‖ ≤ π / (2 * |2k + 1|)`), and connects the positive odd-harmonic
inverse-cube sum `∑' k : ℕ, 1 / (2 * k + 1) ^ 3` to `(7 / 8) * (riemannZeta 3).re`.
-/

open MeasureTheory Metric AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Lemma 1 (Odd-Harmonic Decay Bound):**
For every integer `k : ℤ`, the `(2 * k + 1)`-th Fourier coefficient of
`kuratowskiComplex F x` satisfies `‖f̂_x(2k+1)‖ ≤ π / (2 * |(2 * k + 1 : ℝ)|)`. -/
theorem kuratowski_odd_fourierCoeff_decay (F : IsometricFilling M) (x : M) (k : ℤ) :
    ‖fourierCoeff (kuratowskiComplex F x) (2 * k + 1)‖ ≤
      Real.pi / (2 * |(2 * (k : ℝ) + 1)|) := by
  have h := kuratowski_fourierCoeff_decay F x (2 * k + 1) (by omega)
  push_cast at h
  exact h

/-- **Lemma 2 (Positive Odd-Harmonic Squared-over-Frequency Bound):**
For every natural number `k : ℕ`, `‖f̂_x(2 * k + 1)‖ ^ 2 / (2 * k + 1 : ℝ)` is
bounded above by `(π ^ 2 / 4) * (1 / (2 * k + 1 : ℝ) ^ 3)`. -/
theorem kuratowski_pos_odd_weighted_bound (F : IsometricFilling M) (x : M) (k : ℕ) :
    ‖fourierCoeff (kuratowskiComplex F x) (2 * (k : ℤ) + 1)‖ ^ 2 / (2 * (k : ℝ) + 1) ≤
      (Real.pi ^ 2 / 4) * (1 / (2 * (k : ℝ) + 1) ^ 3) := by
  have hm : 0 < 2 * (k : ℝ) + 1 := by positivity
  have h := kuratowski_odd_fourierCoeff_decay F x (k : ℤ)
  push_cast at h
  rw [abs_of_pos hm] at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [div_le_iff₀ hm]
  calc ‖fourierCoeff (kuratowskiComplex F x) (2 * (k : ℤ) + 1)‖ ^ 2
      ≤ (Real.pi / (2 * (2 * (k : ℝ) + 1))) ^ 2 := h2
    _ = (Real.pi ^ 2 / 4) * (1 / (2 * (k : ℝ) + 1) ^ 3) * (2 * (k : ℝ) + 1) := by
      field_simp
      ring

end

end

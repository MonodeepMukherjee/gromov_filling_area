/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.OddDecaySeries

/-!
# Closed-Form Odd-Harmonic Weighted Spectral Series Bound

This file sums `kuratowski_pos_odd_weighted_bound` over `k : ℕ` and combines it
with `tsum_odd_inv_cube` (`(7 / 8) * ζ(3)`) to prove that the weighted positive
odd-harmonic energy is bounded above by `(7 * π ^ 2 / 32) * (riemannZeta 3).re`.
-/

open MeasureTheory Metric AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The odd-index map `k ↦ 2 * k + 1` on `ℕ` is injective. -/
theorem odd_nat_index_injective : Function.Injective (fun k : ℕ => 2 * k + 1) := by
  intro a b h
  simp only at h
  omega

/-- The positive odd inverse-cube series `∑ 1 / (2k + 1)³` is summable. -/
theorem summable_odd_inv_cube : Summable (fun k : ℕ => (1 : ℝ) / (2 * (k : ℝ) + 1) ^ 3) := by
  have hf : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine (hf.comp_injective odd_nat_index_injective).congr fun k => ?_
  simp [Function.comp_apply]

/-- Each weighted odd-mode energy `‖f̂_x(2k+1)‖² / (2k+1)` is nonnegative. -/
theorem kuratowski_pos_odd_weighted_nonneg (F : IsometricFilling M) (x : M) (k : ℕ) :
    0 ≤ ‖fourierCoeff (kuratowskiComplex F x) (2 * (k : ℤ) + 1)‖ ^ 2 / (2 * (k : ℝ) + 1) :=
  div_nonneg (sq_nonneg _) (by positivity)

/-- **Lemma 1 (Summability of Weighted Positive Odd Fourier Energies):**
The weighted odd-mode series `k ↦ ‖f̂_x(2k+1)‖² / (2k+1)` is summable over `ℕ`. -/
theorem kuratowski_pos_odd_weighted_summable (F : IsometricFilling M) (x : M) :
    Summable (fun k : ℕ =>
      ‖fourierCoeff (kuratowskiComplex F x) (2 * (k : ℤ) + 1)‖ ^ 2 / (2 * (k : ℝ) + 1)) :=
  Summable.of_nonneg_of_le (kuratowski_pos_odd_weighted_nonneg F x)
    (kuratowski_pos_odd_weighted_bound F x) (summable_odd_inv_cube.mul_left _)

/-- **Lemma 2 (Closed-Form Weighted Odd-Harmonic Spectral Bound):**
For every `x : M`, the weighted positive odd-harmonic series is bounded above
by `(7 * π ^ 2 / 32) * (riemannZeta 3).re`. -/
theorem kuratowski_weighted_odd_series_le (F : IsometricFilling M) (x : M) :
    (∑' k : ℕ,
      ‖fourierCoeff (kuratowskiComplex F x) (2 * (k : ℤ) + 1)‖ ^ 2 / (2 * (k : ℝ) + 1)) ≤
      (7 * Real.pi ^ 2 / 32) * (riemannZeta 3).re := by
  calc (∑' k : ℕ,
        ‖fourierCoeff (kuratowskiComplex F x) (2 * (k : ℤ) + 1)‖ ^ 2 / (2 * (k : ℝ) + 1))
      ≤ ∑' k : ℕ, (Real.pi ^ 2 / 4) * (1 / (2 * (k : ℝ) + 1) ^ 3) :=
        Summable.tsum_le_tsum (kuratowski_pos_odd_weighted_bound F x)
          (kuratowski_pos_odd_weighted_summable F x) (summable_odd_inv_cube.mul_left _)
    _ = (Real.pi ^ 2 / 4) * ∑' k : ℕ, (1 : ℝ) / (2 * (k : ℝ) + 1) ^ 3 := tsum_mul_left
    _ = (7 * Real.pi ^ 2 / 32) * (riemannZeta 3).re := by
        rw [tsum_odd_inv_cube]
        ring

end

end

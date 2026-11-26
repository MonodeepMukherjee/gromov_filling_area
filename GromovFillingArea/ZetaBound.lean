/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.FourierBound
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ZetaValues

/-!
# Antipodal Triangle Bound & Odd-Harmonic ζ(3) Series

This file establishes the antipodal sum lower bound `f_x(θ) + f_x(θ + π) ≥ π`
for Kuratowski distance profiles and formalizes the odd-harmonic `7/8 * ζ(3)`
series identity underlying the `14 * ζ(3) / π` filling area lower bound.
-/

open MeasureTheory Metric

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Lemma 1 (Antipodal Triangle Inequality):**
For any `x : M` and `θ : Circle2Pi`, the sum of distances to `θ` and `θ + π`
is at least `dist θ (θ + π)`. -/
theorem kuratowski_antipodal_sum (F : IsometricFilling M) (x : M) (θ : Circle2Pi) :
    dist θ (θ + (Real.pi : Circle2Pi)) ≤
      kuratowskiMap F x θ + kuratowskiMap F x (θ + (Real.pi : Circle2Pi)) := by
  rw [← F.isometry_ι.dist_eq]
  exact dist_triangle_left _ _ x

/-- The even-index terms of `∑ 1 / n ^ 3` contribute `1 / 8` of the full sum. -/
theorem tsum_even_inv_cube :
    (∑' k : ℕ, (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 3) =
      (1 / 8) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 3 := by
  rw [← tsum_mul_left]
  congr 1
  ext k
  push_cast
  rw [mul_pow, one_div, one_div, mul_inv]
  norm_num

/-- The real part of `ζ(3)` is the real series `∑ 1 / n ^ 3`. -/
theorem riemannZeta_three_re :
    (riemannZeta 3).re = ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 3 := by
  have h3 : (3 : ℂ) = ((3 : ℕ) : ℂ) := by norm_num
  rw [h3, zeta_nat_eq_tsum_of_gt_one (by norm_num)]
  have hc : (∑' n : ℕ, 1 / (n : ℂ) ^ 3) =
      ((∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 3 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    push_cast
    rfl
  rw [hc, Complex.ofReal_re]

/-- **Lemma 2 (Odd-Harmonic Series Factor):**
The sum over odd positive integers `∑' k : ℕ, 1 / (2 * k + 1 : ℝ) ^ 3`
equals `(7 / 8) * ζ(3)`. -/
theorem tsum_odd_inv_cube :
    (∑' k : ℕ, (1 : ℝ) / (2 * (k : ℝ) + 1) ^ 3) = (7 / 8) * (riemannZeta 3).re := by
  set f : ℕ → ℝ := fun n ↦ 1 / (n : ℝ) ^ 3 with hf_def
  have hf : Summable f := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have h2 : Function.Injective (fun k : ℕ ↦ 2 * k) := mul_right_injective₀ two_ne_zero
  have he : Summable fun k ↦ f (2 * k) := hf.comp_injective h2
  have ho : Summable fun k ↦ f (2 * k + 1) :=
    hf.comp_injective ((add_left_injective 1).comp h2)
  have hsplit := tsum_even_add_odd he ho
  have heven : (∑' k, f (2 * k)) = (1 / 8) * ∑' n, f n := tsum_even_inv_cube
  have hodd : (∑' k : ℕ, (1 : ℝ) / (2 * (k : ℝ) + 1) ^ 3) = ∑' k, f (2 * k + 1) := by
    simp only [hf_def]
    push_cast
    rfl
  rw [hodd, riemannZeta_three_re]
  linarith

end

end

/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.ZetaBound

/-!
# Quantitative Constant & Boundary Energy Bound

This file proves the numerical lower bound `14 * ζ(3) / π > 0` and links the
antipodal distance inequality to the pointwise maximum lower bound of the
Kuratowski distance profile.
-/

open MeasureTheory Metric

@[expose] public section

noncomputable section

/-- **Lemma 1 (Quantitative Constant Bound):**
The universal lower bound constant `14 * ζ(3) / π` is strictly positive. -/
theorem fourier_constant_pos :
    (0 : ℝ) < 14 * (riemannZeta 3).re / Real.pi := by
  have hsum : Summable fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ 3 :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hζ : 0 < (riemannZeta 3).re := by
    rw [riemannZeta_three_re]
    exact hsum.tsum_pos (fun n ↦ by positivity) 1 (by norm_num)
  exact div_pos (by positivity) Real.pi_pos

/-- **Lemma 2 (Antipodal Maximum Lower Bound):**
At any angle `θ`, at least one of `kuratowskiMap F x θ` or
`kuratowskiMap F x (θ + π)` is at least `(1 / 2) * dist θ (θ + π)`. -/
theorem kuratowski_antipodal_max {M : Type*} [MetricSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (F : IsometricFilling M) (x : M) (θ : Circle2Pi) :
    (1 / 2 : ℝ) * dist θ (θ + (Real.pi : Circle2Pi)) ≤
      max (kuratowskiMap F x θ) (kuratowskiMap F x (θ + (Real.pi : Circle2Pi))) := by
  have hsum := kuratowski_antipodal_sum F x θ
  have h₁ := le_max_left (kuratowskiMap F x θ)
    (kuratowskiMap F x (θ + (Real.pi : Circle2Pi)))
  have h₂ := le_max_right (kuratowskiMap F x θ)
    (kuratowskiMap F x (θ + (Real.pi : Circle2Pi)))
  linarith

end

end

/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.Kuratowski
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Harmonic Analysis & Fourier Lower Bound Setup

This file lifts the Kuratowski distance profile to periodic Lipschitz functions
on `ℝ` and sets up the Fourier coefficient and Wirtinger energy inequalities
needed for the `14 * ζ(3) / π` universal area lower bound.
-/

open MeasureTheory Metric

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Lift `kuratowskiMap F x` from `Circle2Pi` to a `2π`-periodic real function. -/
def periodicDistance (F : IsometricFilling M) (x : M) (t : ℝ) : ℝ :=
  kuratowskiMap F x (t : Circle2Pi)

/-- **Lemma 1:** `periodicDistance F x` is `2π`-periodic on `ℝ`. -/
theorem periodicDistance_periodic (F : IsometricFilling M) (x : M) :
    Function.Periodic (periodicDistance F x) (2 * Real.pi) := by
  intro t
  simp only [periodicDistance, AddCircle.coe_add_period]

/-- The quotient map `ℝ → Circle2Pi` is 1-Lipschitz. -/
theorem circle2Pi_coe_lipschitz : LipschitzWith 1 (fun t : ℝ ↦ (t : Circle2Pi)) := by
  refine LipschitzWith.of_dist_le_mul fun a b ↦ ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

/-- For fixed `x : M`, `kuratowskiMap F x` is 1-Lipschitz on `Circle2Pi`. -/
theorem kuratowskiMap_lipschitzWith (F : IsometricFilling M) (x : M) :
    LipschitzWith 1 (kuratowskiMap F x) := by
  refine LipschitzWith.of_dist_le_mul fun θ₁ θ₂ ↦ ?_
  rw [NNReal.coe_one, one_mul, Real.dist_eq]
  exact kuratowski_lipschitz F x θ₁ θ₂

/-- **Lemma 2:** `periodicDistance F x` is 1-Lipschitz on `ℝ`. -/
theorem periodicDistance_lipschitz (F : IsometricFilling M) (x : M) :
    LipschitzWith 1 (periodicDistance F x) := by
  have h := (kuratowskiMap_lipschitzWith F x).comp circle2Pi_coe_lipschitz
  rwa [one_mul] at h

end

end

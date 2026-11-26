/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.Basic

/-!
# Kuratowski Isometric Embedding for Gromov's Filling Area Conjecture

This file defines the Kuratowski distance profile map `x ↦ (θ ↦ dist x (F.ι θ))`
and establishes its 1-Lipschitz and non-expansive metric properties.
-/

open MeasureTheory Metric

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The Kuratowski distance function associated to an interior point `x : M`. -/
def kuratowskiMap (F : IsometricFilling M) (x : M) (θ : Circle2Pi) : ℝ :=
  dist x (F.ι θ)

/-- **Lemma 1:** For fixed `x : M`, the distance profile `θ ↦ dist x (F.ι θ)`
is 1-Lipschitz. -/
theorem kuratowski_lipschitz (F : IsometricFilling M) (x : M) (θ₁ θ₂ : Circle2Pi) :
    |kuratowskiMap F x θ₁ - kuratowskiMap F x θ₂| ≤ dist θ₁ θ₂ := by
  unfold kuratowskiMap
  rw [dist_comm x, dist_comm x, ← F.isometry_ι.dist_eq θ₁ θ₂]
  exact abs_dist_sub_le (F.ι θ₁) (F.ι θ₂) x

/-- **Lemma 2:** Moving `x` to `y` in `M` changes `kuratowskiMap` pointwise
by at most `dist x y`. -/
theorem kuratowski_nonexpansive (F : IsometricFilling M) (x y : M) (θ : Circle2Pi) :
    |kuratowskiMap F x θ - kuratowskiMap F y θ| ≤ dist x y :=
  abs_dist_sub_le x y (F.ι θ)

end

end

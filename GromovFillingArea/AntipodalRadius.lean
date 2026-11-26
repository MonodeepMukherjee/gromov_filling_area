/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.FourierEnergy
public import GromovFillingArea.Witness

/-!
# Antipodal Diameter & Inradius Lower Bound

This file proves that antipodal points `θ` and `θ + π` on `Circle2Pi` have
exact geodesic distance `π`, yielding the sharp pointwise lower bound
`π / 2 ≤ max (kuratowskiMap F x θ) (kuratowskiMap F x (θ + π))`.
-/

open MeasureTheory Metric

@[expose] public section

noncomputable section

/-- **Lemma 1 (Exact Antipodal Distance):**
For any `θ : Circle2Pi`, the distance to its antipodal point `θ + π` is `π`. -/
theorem circle2Pi_dist_add_pi (θ : Circle2Pi) :
    dist θ (θ + (Real.pi : Circle2Pi)) = Real.pi := by
  have h := AddCircle.norm_half_period_eq (2 * Real.pi)
  rw [abs_of_pos Real.two_pi_pos, show 2 * Real.pi / 2 = Real.pi by ring] at h
  rw [dist_comm, dist_eq_norm, add_sub_cancel_left]
  exact h

/-- **Lemma 2 (Sharp Half-Period Radius Bound):**
For every interior point `x : M` and boundary angle `θ : Circle2Pi`, at least
one of `dist x (F.ι θ)` or `dist x (F.ι (θ + π))` is at least `π / 2`. -/
theorem kuratowski_half_pi_bound {M : Type*} [MetricSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (F : IsometricFilling M) (x : M) (θ : Circle2Pi) :
    Real.pi / 2 ≤
      max (kuratowskiMap F x θ) (kuratowskiMap F x (θ + (Real.pi : Circle2Pi))) := by
  have h := kuratowski_antipodal_max F x θ
  rw [circle2Pi_dist_add_pi] at h
  linarith

end

end

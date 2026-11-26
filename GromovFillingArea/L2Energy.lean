/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.AntipodalRadius
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Squared Antipodal Energy & Continuity on `Circle2Pi`

This file establishes the pointwise `L²` antipodal lower bound
`π ^ 2 / 2 ≤ (f_x θ) ^ 2 + (f_x (θ + π)) ^ 2` and proves continuity of the
periodic distance profile `periodicDistance F x` for interval integration.
-/

open MeasureTheory Metric

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Lemma 1 (Pointwise Squared Antipodal Inequality):**
The sum of squared distances to antipodal boundary points `θ` and `θ + π`
is at least `π ^ 2 / 2`. -/
theorem kuratowski_antipodal_sq_sum (F : IsometricFilling M) (x : M) (θ : Circle2Pi) :
    Real.pi ^ 2 / 2 ≤
      (kuratowskiMap F x θ) ^ 2 + (kuratowskiMap F x (θ + (Real.pi : Circle2Pi))) ^ 2 := by
  have h := kuratowski_antipodal_sum F x θ
  rw [circle2Pi_dist_add_pi] at h
  nlinarith [sq_nonneg (kuratowskiMap F x θ - kuratowskiMap F x (θ + (Real.pi : Circle2Pi))),
    Real.pi_pos]

/-- **Lemma 2 (Continuity of Periodic Distance Lift):**
`periodicDistance F x` is continuous on `ℝ` (hence interval-integrable on `[0, 2π]`). -/
theorem periodicDistance_continuous (F : IsometricFilling M) (x : M) :
    Continuous (periodicDistance F x) :=
  (periodicDistance_lipschitz F x).continuous

end

end

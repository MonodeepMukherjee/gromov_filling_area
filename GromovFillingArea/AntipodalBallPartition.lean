/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.SliceCoareaBound

/-!
# Antipodal Boundary Half-Ball Partition & Area Additivity

Motivated by the numerical boundary-averaged half-ball areas
`mean_θ Area(B_M(ι θ, π/2)) ≈ 0.9998π, 1.015π, 1.071π` on the certified genus `0, 1, 2`
metrics (`π` is `4` in `μH` units; the genus-0 value equals `π` up to discretization),
this file proves directly from `kuratowski_antipodal_sum` that for every angle `θ`,
the two antipodal open boundary balls `Metric.ball (F.ι θ) (π / 2)` and
`Metric.ball (F.ι (θ + π)) (π / 2)` are disjoint in `M`, so the sum of their
`2`-dimensional Hausdorff measures is at most `μH (univ : Set M)`:
`μH (ball (F.ι θ) (π / 2)) + μH (ball (F.ι (θ + π)) (π / 2)) ≤ μH univ`.
-/

open MeasureTheory Metric Set AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Lemma 1 (Disjointness of Antipodal Boundary Half-Balls):**
For every `F : IsometricFilling M` and `θ : Circle2Pi`, the open metric balls
of radius `π / 2` centered at `F.ι θ` and `F.ι (θ + π)` are disjoint. -/
theorem antipodal_boundary_balls_disjoint (F : IsometricFilling M) (θ : Circle2Pi) :
    Disjoint (Metric.ball (F.ι θ) (Real.pi / 2))
      (Metric.ball (F.ι (θ + (Real.pi : Circle2Pi))) (Real.pi / 2)) := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  rw [Metric.mem_ball] at hx₁ hx₂
  have hsum := kuratowski_antipodal_sum F x θ
  rw [circle2Pi_dist_add_pi] at hsum
  simp only [kuratowskiMap] at hsum
  linarith

/-- **Lemma 2 (Antipodal Half-Ball Area Additivity Bound):**
For every `F : IsometricFilling M` and `θ : Circle2Pi`, the sum of the
`2`-dimensional Hausdorff measures of the antipodal boundary half-balls
`ball (F.ι θ) (π / 2)` and `ball (F.ι (θ + π)) (π / 2)` is at most
`hausdorffMeasure 2 (univ : Set M)`. -/
theorem antipodal_boundary_balls_hausdorffMeasure_le (F : IsometricFilling M) (θ : Circle2Pi) :
    MeasureTheory.Measure.hausdorffMeasure 2 (Metric.ball (F.ι θ) (Real.pi / 2)) +
      MeasureTheory.Measure.hausdorffMeasure 2
        (Metric.ball (F.ι (θ + (Real.pi : Circle2Pi))) (Real.pi / 2)) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) := by
  rw [← measure_union (antipodal_boundary_balls_disjoint F θ) Metric.isOpen_ball.measurableSet]
  exact measure_mono (subset_univ _)

end

end

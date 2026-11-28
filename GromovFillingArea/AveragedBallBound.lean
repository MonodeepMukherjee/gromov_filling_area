/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.AntipodalBallPartition

/-!
# Haar-Averaged Antipodal Half-Ball Area & Reduction to `4 ≤ meanBoundaryBall`

This file integrates `antipodal_boundary_balls_hausdorffMeasure_le` over `Circle2Pi`
with respect to the normalized Haar probability measure `haarAddCircle`, proving:
1. `2 * ∫ θ, (μH (ball (F.ι θ) (π / 2))).toReal ∂haarAddCircle ≤ (μH univ).toReal`
   (when `μH univ ≠ ⊤`).
2. Whenever the Haar-averaged boundary half-ball measure is at least `4`
   (`= Riemannian π`), the full conjectured lower bound `(8 : ENNReal) ≤ μH univ`
   follows immediately.
-/

open MeasureTheory Metric Set AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Real-valued `2`-dimensional Hausdorff measure of the boundary half-ball `B(F.ι θ, π / 2)`. -/
def boundaryBallMeasureReal (F : IsometricFilling M) (θ : Circle2Pi) : ℝ :=
  (MeasureTheory.Measure.hausdorffMeasure 2
    (Metric.ball (F.ι θ) (Real.pi / 2))).toReal

/-- **Lemma 1 (Haar-Averaged Antipodal Half-Ball Inequality):**
If `M` has finite `2`-dimensional Hausdorff measure (`μH univ ≠ ⊤`) and
`boundaryBallMeasureReal F` is integrable on `Circle2Pi`, then twice its Haar
average is at most `(μH univ).toReal`. -/
theorem two_mul_haar_integral_boundaryBall_le (F : IsometricFilling M)
    (h_fin : MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) ≠ ⊤)
    (h_int : Integrable (boundaryBallMeasureReal F) haarAddCircle) :
    2 * (∫ θ : Circle2Pi, boundaryBallMeasureReal F θ ∂haarAddCircle) ≤
      (MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M)).toReal := by
  set f := boundaryBallMeasureReal F with hf_def
  have hpt : ∀ θ : Circle2Pi, f θ + f (θ + (Real.pi : Circle2Pi)) ≤
      (MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M)).toReal := by
    intro θ
    have h := antipodal_boundary_balls_hausdorffMeasure_le F θ
    have hA : MeasureTheory.Measure.hausdorffMeasure 2
        (Metric.ball (F.ι θ) (Real.pi / 2)) ≠ ⊤ :=
      ne_top_of_le_ne_top h_fin (measure_mono (subset_univ _))
    have hB : MeasureTheory.Measure.hausdorffMeasure 2
        (Metric.ball (F.ι (θ + (Real.pi : Circle2Pi))) (Real.pi / 2)) ≠ ⊤ :=
      ne_top_of_le_ne_top h_fin (measure_mono (subset_univ _))
    rw [hf_def, boundaryBallMeasureReal, boundaryBallMeasureReal,
      ← ENNReal.toReal_add hA hB]
    exact ENNReal.toReal_mono h_fin h
  have h_int2 : Integrable (fun θ => f (θ + (Real.pi : Circle2Pi))) haarAddCircle :=
    h_int.comp_add_right _
  have h_mono : (∫ θ : Circle2Pi, (f θ + f (θ + (Real.pi : Circle2Pi))) ∂haarAddCircle) ≤
      ∫ _θ : Circle2Pi,
        (MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M)).toReal ∂haarAddCircle :=
    integral_mono (h_int.add h_int2) (integrable_const _) hpt
  rw [integral_add h_int h_int2, integral_add_right_eq_self, integral_const,
    probReal_univ, one_smul] at h_mono
  linarith

/-- **Lemma 2 (Full `8` Lower Bound from Mean Half-Ball Measure `≥ 4`):**
If the Haar-averaged boundary half-ball measure satisfies
`4 ≤ ∫ θ : Circle2Pi, boundaryBallMeasureReal F θ ∂haarAddCircle` (and `h_int`),
then `(8 : ENNReal) ≤ MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M)`. -/
theorem gromov_conjecture_of_mean_boundaryBall_ge_four (F : IsometricFilling M)
    (h_int : Integrable (boundaryBallMeasureReal F) haarAddCircle)
    (h_mean : 4 ≤ ∫ θ : Circle2Pi, boundaryBallMeasureReal F θ ∂haarAddCircle) :
    (8 : ENNReal) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) := by
  by_cases h_fin : MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) = ⊤
  · rw [h_fin]
    exact le_top
  · have h := two_mul_haar_integral_boundaryBall_le F h_fin h_int
    rw [← ENNReal.ofReal_ofNat 8]
    exact ENNReal.ofReal_le_of_le_toReal (by linarith)

end

end

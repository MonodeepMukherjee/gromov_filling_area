/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.CapExcessThreshold

/-!
# Local Half-Ball `L^∞_2` Projection & Exact Lebesgue Area Lower Bound

For each boundary anchor `θ₀ : Circle2Pi`, this file defines the `1`-Lipschitz
two-anchor map `twoAnchorMap F θ₀ : M → (Fin 2 → ℝ)` given by
`x ↦ ![dist x (F.ι θ₀), dist x (F.ι (θ₀ + π / 2))]` and proves:
1. `LipschitzWith 1 (twoAnchorMap F θ₀)` with respect to the `L^∞` sup-metric on `Fin 2 → ℝ`.
2. On the open boundary half-ball `B(F.ι θ₀, π / 2)`, the `2`-dimensional Lebesgue
   volume of its image in `Fin 2 → ℝ` is bounded above by `μH (ball (F.ι θ₀) (π / 2))`.
-/

open MeasureTheory Metric Set AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Two-anchor `L^∞_2` projection `x ↦ ![dist x (F.ι θ₀), dist x (F.ι (θ₀ + π / 2))]`. -/
def twoAnchorMap (F : IsometricFilling M) (θ₀ : Circle2Pi) (x : M) : Fin 2 → ℝ :=
  ![dist x (F.ι θ₀), dist x (F.ι (θ₀ + ((Real.pi / 2 : ℝ) : Circle2Pi)))]

/-- **Lemma 1 (1-Lipschitz Property of `twoAnchorMap F θ₀`):**
With the `L^∞` sup-metric on `Fin 2 → ℝ`, `twoAnchorMap F θ₀` is `1`-Lipschitz. -/
theorem twoAnchorMap_lipschitzWith (F : IsometricFilling M) (θ₀ : Circle2Pi) :
    LipschitzWith 1 (twoAnchorMap F θ₀) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul]
  refine (dist_pi_le_iff dist_nonneg).2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · change dist (dist x (F.ι θ₀)) (dist y (F.ι θ₀)) ≤ dist x y
    rw [Real.dist_eq]
    exact abs_dist_sub_le x y _
  · change dist (dist x (F.ι (θ₀ + ((Real.pi / 2 : ℝ) : Circle2Pi))))
      (dist y (F.ι (θ₀ + ((Real.pi / 2 : ℝ) : Circle2Pi)))) ≤ dist x y
    rw [Real.dist_eq]
    exact abs_dist_sub_le x y _

/-- **Lemma 2 (Local Half-Ball Volume Bound in `Fin 2 → ℝ`):**
For every `θ₀ : Circle2Pi`, the `2`-dimensional Lebesgue volume of
`twoAnchorMap F θ₀ '' Metric.ball (F.ι θ₀) (Real.pi / 2)` in `Fin 2 → ℝ` is at most
`MeasureTheory.Measure.hausdorffMeasure 2 (Metric.ball (F.ι θ₀) (Real.pi / 2))`. -/
theorem volume_twoAnchorMap_ball_le (F : IsometricFilling M) (θ₀ : Circle2Pi) :
    volume (twoAnchorMap F θ₀ '' Metric.ball (F.ι θ₀) (Real.pi / 2)) ≤
      MeasureTheory.Measure.hausdorffMeasure 2
        (Metric.ball (F.ι θ₀) (Real.pi / 2)) := by
  have hvol : (volume : Measure (Fin 2 → ℝ)) = MeasureTheory.Measure.hausdorffMeasure 2 := by
    rw [← hausdorffMeasure_pi_real]
    norm_num
  have himg := (twoAnchorMap_lipschitzWith F θ₀).hausdorffMeasure_image_le (d := 2)
    (by norm_num) (Metric.ball (F.ι θ₀) (Real.pi / 2))
  rw [ENNReal.coe_one, ENNReal.one_rpow, one_mul] at himg
  rw [hvol]
  exact himg

end

end

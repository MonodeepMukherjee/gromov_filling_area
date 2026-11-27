/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.KuratowskiEmbedding

/-!
# 2-Dimensional Hausdorff Area Contraction Under Kuratowski Embedding

This file proves that the Kuratowski Banach-space embedding `kuratowskiBanach F`
(and any `1`-Lipschitz projection `Φ : (Circle2Pi →ᵇ ℝ) → Y` out of it) does not
increase `2`-dimensional Hausdorff measure (`hausdorffMeasure 2`), bridging
metric area in `M` to projected areas in `L^∞(S¹)`.
-/

open MeasureTheory Metric Set BoundedContinuousFunction

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The Borel `σ`-algebra on `Circle2Pi →ᵇ ℝ` (sup-norm topology), used for Hausdorff measure. -/
instance BoundedContinuousFunction.circle2PiMeasurableSpace : MeasurableSpace (Circle2Pi →ᵇ ℝ) :=
  borel _

instance BoundedContinuousFunction.circle2PiBorelSpace : BorelSpace (Circle2Pi →ᵇ ℝ) :=
  ⟨rfl⟩

/-- A `1`-Lipschitz map does not increase the `2`-dimensional Hausdorff measure:
`μH[2] (range f) ≤ μH[2] univ`. -/
theorem lipschitzWith_one_hausdorffMeasure_range_le {X Y : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (f : X → Y) (hf : LipschitzWith 1 f) :
    MeasureTheory.Measure.hausdorffMeasure 2 (range f) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set X) := by
  have h := hf.hausdorffMeasure_image_le (d := 2) (by norm_num) univ
  rwa [image_univ, ENNReal.coe_one, ENNReal.one_rpow, one_mul] at h

/-- **Lemma 1 (Hausdorff Area Contraction in `L^∞(S¹)`):**
The `2`-dimensional Hausdorff measure of the Kuratowski image `range (kuratowskiBanach F)`
is at most the `2`-dimensional Hausdorff measure of `M`. -/
theorem kuratowskiBanach_hausdorffMeasure_le (F : IsometricFilling M) :
    MeasureTheory.Measure.hausdorffMeasure 2 (range (kuratowskiBanach F)) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) :=
  lipschitzWith_one_hausdorffMeasure_range_le _ (kuratowskiBanach_lipschitzWith F)

/-- **Lemma 2 (1-Lipschitz Projection Area Contraction):**
For any metric space `Y` and any `1`-Lipschitz map `π : (Circle2Pi →ᵇ ℝ) → Y`,
the `2`-dimensional Hausdorff measure of `range (π ∘ kuratowskiBanach F)` is at
most `hausdorffMeasure 2 (univ : Set M)`. -/
theorem kuratowskiBanach_proj_hausdorffMeasure_le (F : IsometricFilling M)
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (π : (Circle2Pi →ᵇ ℝ) → Y) (hπ : LipschitzWith 1 π) :
    MeasureTheory.Measure.hausdorffMeasure 2 (range (π ∘ kuratowskiBanach F)) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) := by
  have hL : LipschitzWith 1 (π ∘ kuratowskiBanach F) := by
    simpa using hπ.comp (kuratowskiBanach_lipschitzWith F)
  exact lipschitzWith_one_hausdorffMeasure_range_le _ hL

end

end

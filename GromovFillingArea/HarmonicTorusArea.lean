/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.HarmonicTorusBoundary

/-!
# Higher-Dimensional `L^∞` Torus Filling Criterion & `4 / π` Recovery

This file connects `MultiModeVectorEmbedding` and `HarmonicTorusBoundary` directly
to the area of `M`:
1. For every `1 ≤ K`, projecting `range (oddHarmonicVectorMap K ∘ kuratowskiBanach F)`
   onto its `0`-th coordinate recovers the fundamental `4 / π` lower bound on the
   `2`-dimensional `L^∞` Hausdorff measure of the higher-dimensional image itself
   (under the no-retraction hypothesis `h_no_retract`).
2. Whenever the `L^∞` Hausdorff measure of `range (oddHarmonicVectorMap K ∘ kuratowskiBanach F)`
   is at least `8` (the asymptotic multi-mode ceiling `a + b/K → 8`), the full
   Gromov Filling Area Conjecture `(8 : ENNReal) ≤ μH (univ : Set M)` follows
   immediately from `kuratowski_oddHarmonicVectorMap_hausdorffMeasure_le`.
-/

open MeasureTheory Metric Set BoundedContinuousFunction AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Lemma 1 (`4 / π` Lower Bound on the Higher-Dimensional Torus Image):**
For any `F : IsometricFilling M` satisfying `h_no_retract` and any `1 ≤ K`,
the `2`-dimensional Hausdorff measure of `range (oddHarmonicVectorMap K ∘ kuratowskiBanach F)`
in `Fin K → ℂ` is at least `ENNReal.ofReal (4 / Real.pi)`. -/
theorem oddHarmonicVectorMap_image_hausdorffMeasure_ge_four_div_pi
    (F : IsometricFilling M) {K : ℕ} (hK : 1 ≤ K)
    (h_no_retract : ¬ ∃ r : M → Circle2Pi, Continuous r ∧ ∀ θ : Circle2Pi, r (F.ι θ) = θ) :
    ENNReal.ofReal (4 / Real.pi) ≤
      MeasureTheory.Measure.hausdorffMeasure 2
        (range (oddHarmonicVectorMap K ∘ kuratowskiBanach F)) := by
  set f : M → ℂ := fourierProj 1 ∘ kuratowskiBanach F with hf_def
  have hcont : Continuous f :=
    (fourierProj_lipschitzWith 1).continuous.comp (kuratowskiBanach_lipschitzWith F).continuous
  have h_fill : Metric.closedBall (0 : ℂ) (2 / Real.pi) ⊆ range f :=
    disk_covered_of_no_retraction F (by positivity) f hcont
      (fourierProjOneBoundaryHomeomorph F) (fun _ => rfl) h_no_retract
  have h_eval : LipschitzWith 1 (fun v : Fin K → ℂ => v ⟨0, hK⟩) := by
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    rw [NNReal.coe_one, one_mul]
    exact dist_le_pi_dist v w ⟨0, hK⟩
  have h_range : range f =
      (fun v : Fin K → ℂ => v ⟨0, hK⟩) '' range (oddHarmonicVectorMap K ∘ kuratowskiBanach F) := by
    rw [← range_comp]
    rfl
  calc ENNReal.ofReal (4 / Real.pi)
      ≤ MeasureTheory.Measure.hausdorffMeasure 2 (Metric.closedBall (0 : ℂ) (2 / Real.pi)) :=
        hausdorffMeasure_two_fundamental_disk
    _ ≤ MeasureTheory.Measure.hausdorffMeasure 2 (range f) := measure_mono h_fill
    _ ≤ MeasureTheory.Measure.hausdorffMeasure 2
          (range (oddHarmonicVectorMap K ∘ kuratowskiBanach F)) := by
        rw [h_range]
        simpa using h_eval.hausdorffMeasure_image_le (d := 2) (by norm_num)
          (range (oddHarmonicVectorMap K ∘ kuratowskiBanach F))

/-- **Lemma 2 (Gromov's `8` Lower Bound from Higher-Dimensional Torus Filling):**
If for some `K : ℕ` the `2`-dimensional `L^∞` Hausdorff measure of
`range (oddHarmonicVectorMap K ∘ kuratowskiBanach F)` in `Fin K → ℂ` is at least `8`,
then `(8 : ENNReal) ≤ MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M)`. -/
theorem gromov_conjecture_of_harmonic_torus_area_ge_eight
    (F : IsometricFilling M) (K : ℕ)
    (h_torus : (8 : ENNReal) ≤
      MeasureTheory.Measure.hausdorffMeasure 2
        (range (oddHarmonicVectorMap K ∘ kuratowskiBanach F))) :
    (8 : ENNReal) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) :=
  le_trans h_torus (kuratowski_oddHarmonicVectorMap_hausdorffMeasure_le F K)

end

end

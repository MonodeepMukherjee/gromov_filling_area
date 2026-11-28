/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.HarmonicTorusArea

/-!
# Multi-Harmonic Disk Covering on Every Odd Mode

This file generalizes the fundamental-mode (`n = 1`) disk bound of `UniversalAreaBound`
to every odd frequency `n = 2k + 1`:
1. The `(2k + 1)`-th boundary map `θ₀ ↦ fourierProj (2k + 1) (kuratowskiBanach F (F.ι θ₀))`
   lands on the circle of radius `R_{2k+1} = 2 / ((2k + 1)² π)`.
2. If the `(2k + 1)`-th mode image covers the closed disk of radius `R_{2k+1}`
   (hypothesis `h_cover`), then for every `k < K` the `2`-dimensional Hausdorff measure of
   `range (oddHarmonicVectorMap K ∘ kuratowskiBanach F)` is at least
   `π R_{2k+1}² = 4 / ((2k + 1)⁴ π)`.

For `k ≥ 1` the boundary map winds `2k + 1` times, so it is not a homeomorphism onto the
circle and `disk_covered_of_no_retraction` does not apply directly. The covering hypothesis
is therefore kept explicit here.
-/

open MeasureTheory Metric Set BoundedContinuousFunction AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The radius `R_{2k+1} = 2 / ((2k + 1)² π)` of the `(2k + 1)`-th boundary circle. -/
def oddModeRadius (k : ℕ) : ℝ := 2 / ((2 * (k : ℝ) + 1) ^ 2 * Real.pi)

theorem oddModeRadius_pos (k : ℕ) : 0 < oddModeRadius k := by
  unfold oddModeRadius
  have := Real.pi_pos
  positivity

/-- **Lemma 1 (Odd-Mode Boundary Circle):** the `(2k + 1)`-th boundary map lands on the
sphere of radius `2 / ((2k + 1)² π)` in `ℂ`. -/
theorem fourierProj_odd_boundary_mem_sphere (F : IsometricFilling M) (k : ℕ)
    (θ₀ : Circle2Pi) :
    fourierProj (2 * (k : ℤ) + 1) (kuratowskiBanach F (F.ι θ₀)) ∈
      Metric.sphere (0 : ℂ) (2 / ((2 * (k : ℝ) + 1) ^ 2 * Real.pi)) := by
  rw [mem_sphere_zero_iff_norm, fourierProj_boundary_eq F (2 * (k : ℤ) + 1) θ₀, norm_mul,
    fourier_norm_apply, one_mul]
  exact fourierProj_boundary_odd_norm F k

/-- The Lebesgue area of the closed disk of radius `R_{2k+1}` is `4 / ((2k + 1)⁴ π)`. -/
theorem volume_oddMode_disk (k : ℕ) :
    volume (Metric.closedBall (0 : ℂ) (oddModeRadius k)) =
      ENNReal.ofReal (4 / ((2 * (k : ℝ) + 1) ^ 4 * Real.pi)) := by
  have hπ := Real.pi_pos
  have hk : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  rw [Complex.volume_closedBall, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_pow (oddModeRadius_pos k).le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold oddModeRadius
  field_simp
  ring

/-- Evaluation at a coordinate of `Fin K → ℂ` is `1`-Lipschitz for the sup metric. -/
theorem lipschitzWith_eval_fin {K : ℕ} (j : Fin K) :
    LipschitzWith 1 (fun v : Fin K → ℂ => v j) := by
  refine LipschitzWith.of_dist_le_mul fun v w => ?_
  rw [NNReal.coe_one, one_mul]
  exact dist_le_pi_dist v w j

/-- `μH[2]` does not increase under `1`-Lipschitz maps into `ℂ` from `Fin K → ℂ`. -/
theorem hausdorffMeasure_image_eval_le {K : ℕ} (j : Fin K) (s : Set (Fin K → ℂ)) :
    MeasureTheory.Measure.hausdorffMeasure 2 ((fun v : Fin K → ℂ => v j) '' s) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 s := by
  simpa using (lipschitzWith_eval_fin j).hausdorffMeasure_image_le (d := 2) (by norm_num) s

/-- **Lemma 2 (Odd-Mode Coordinate Area Lower Bound):** if the `(2k + 1)`-th mode image
covers the closed disk of radius `R_{2k+1}`, then for every `k < K` the `L^∞` image
`range (oddHarmonicVectorMap K ∘ kuratowskiBanach F)` has `μH[2] ≥ 4 / ((2k + 1)⁴ π)`. -/
theorem oddHarmonicVectorMap_coord_area_lower_bound (F : IsometricFilling M)
    {K k : ℕ} (hk : k < K)
    (h_cover : Metric.closedBall (0 : ℂ) (2 / ((2 * (k : ℝ) + 1) ^ 2 * Real.pi)) ⊆
      range (fourierProj (2 * (k : ℤ) + 1) ∘ kuratowskiBanach F)) :
    ENNReal.ofReal (4 / ((2 * (k : ℝ) + 1) ^ 4 * Real.pi)) ≤
      MeasureTheory.Measure.hausdorffMeasure 2
        (range (oddHarmonicVectorMap K ∘ kuratowskiBanach F)) := by
  have h_range : range (fourierProj (2 * (k : ℤ) + 1) ∘ kuratowskiBanach F) =
      (fun v : Fin K → ℂ => v ⟨k, hk⟩) ''
        range (oddHarmonicVectorMap K ∘ kuratowskiBanach F) := by
    rw [← range_comp]
    rfl
  calc ENNReal.ofReal (4 / ((2 * (k : ℝ) + 1) ^ 4 * Real.pi))
      = volume (Metric.closedBall (0 : ℂ) (oddModeRadius k)) := (volume_oddMode_disk k).symm
    _ ≤ MeasureTheory.Measure.hausdorffMeasure 2
          (Metric.closedBall (0 : ℂ) (oddModeRadius k)) :=
        volume_le_hausdorffMeasure_two_complex _
    _ ≤ MeasureTheory.Measure.hausdorffMeasure 2
          (range (fourierProj (2 * (k : ℤ) + 1) ∘ kuratowskiBanach F)) :=
        measure_mono h_cover
    _ ≤ _ := by
        rw [h_range]
        exact hausdorffMeasure_image_eval_le _ _

end

end

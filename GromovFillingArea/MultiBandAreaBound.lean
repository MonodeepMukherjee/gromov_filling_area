/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.OddModeDiskCovering

/-!
# Disjoint Frequency-Band Area Decomposition in `Fin 2 → ℂ`

Let `S = range (oddHarmonicVectorMap 2 ∘ kuratowskiBanach F) ⊆ Fin 2 → ℂ`, the image of `M`
under `x ↦ (f̂_x(1), f̂_x(3))` with the sup metric. With `R₁ = 2 / π` and `R₃ = 2 / (9π)`:
1. `bandCore = {v | ‖v 0‖ ≤ R₃}` and `bandAnnulus = {v | R₃ < ‖v 0‖}` are disjoint Borel sets
   that partition `Fin 2 → ℂ`, so `μH[2] S = μH[2] (S ∩ bandCore) + μH[2] (S ∩ bandAnnulus)`.
2. Under the no-retraction hypothesis, the `0`-th coordinate maps `S ∩ bandAnnulus` onto a set
   containing the planar annulus `R₃ < ‖z‖ ≤ R₁`, of area `π (R₁² − R₃²) = 320 / (81π)`.
   Hence `320 / (81π) ≤ μH[2] (S ∩ bandAnnulus)`.
3. Consequently `320 / (81π) + μH[2] (S ∩ bandCore) ≤ μH[2] univ`.

A lower bound on `μH[2] (S ∩ bandCore)` is **not** proved here. Exceeding `4 / π` this way
would need `μH[2] (S ∩ bandCore) > 4 / (81π)`; the points of `M` where `f̂(3)` covers its
disk need not have `‖f̂(1)‖ ≤ R₃`, so this does not follow from the `3`-mode disk alone.
-/

open MeasureTheory Metric Set BoundedContinuousFunction AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The core band `‖v 0‖ ≤ 2 / (9π)` in `Fin 2 → ℂ`. -/
def bandCore : Set (Fin 2 → ℂ) := {v | ‖v 0‖ ≤ 2 / (9 * Real.pi)}

/-- The outer band `2 / (9π) < ‖v 0‖` in `Fin 2 → ℂ`. -/
def bandAnnulus : Set (Fin 2 → ℂ) := {v | 2 / (9 * Real.pi) < ‖v 0‖}

/-- The planar annulus `2 / (9π) < ‖z‖ ≤ 2 / π` in `ℂ`. -/
def planarOuterAnnulus : Set ℂ := {z | 2 / (9 * Real.pi) < ‖z‖ ∧ ‖z‖ ≤ 2 / Real.pi}

theorem bandCore_disjoint_bandAnnulus : Disjoint bandCore bandAnnulus := by
  rw [Set.disjoint_left]
  intro v (h1 : ‖v 0‖ ≤ 2 / (9 * Real.pi)) (h2 : 2 / (9 * Real.pi) < ‖v 0‖)
  exact absurd h1 (not_le.mpr h2)

theorem bandAnnulus_eq_compl : bandAnnulus = bandCoreᶜ := by
  ext v
  simp [bandCore, bandAnnulus]

theorem measurableSet_bandCore : MeasurableSet bandCore :=
  (isClosed_le (continuous_norm.comp (continuous_apply 0)) continuous_const).measurableSet

theorem measurableSet_bandAnnulus : MeasurableSet bandAnnulus := by
  rw [bandAnnulus_eq_compl]
  exact measurableSet_bandCore.compl

/-- **Lemma 1 (Exact Two-Band Decomposition):** for every `S ⊆ Fin 2 → ℂ`,
`μH[2] S = μH[2] (S ∩ bandCore) + μH[2] (S ∩ bandAnnulus)`. -/
theorem hausdorffMeasure_band_decomposition (S : Set (Fin 2 → ℂ)) :
    MeasureTheory.Measure.hausdorffMeasure 2 S =
      MeasureTheory.Measure.hausdorffMeasure 2 (S ∩ bandCore) +
        MeasureTheory.Measure.hausdorffMeasure 2 (S ∩ bandAnnulus) := by
  rw [bandAnnulus_eq_compl, ← sdiff_eq]
  exact (measure_inter_add_sdiff S measurableSet_bandCore).symm

/-- Lebesgue area of a closed disk in `ℂ` centred at `0`. -/
theorem volume_closedBall_zero_complex {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.closedBall (0 : ℂ) r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [Complex.volume_closedBall, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (by positivity), mul_comm]

theorem planarOuterAnnulus_eq :
    planarOuterAnnulus =
      Metric.closedBall (0 : ℂ) (2 / Real.pi) \ Metric.closedBall 0 (2 / (9 * Real.pi)) := by
  ext z
  simp only [planarOuterAnnulus, mem_ofPred_eq, mem_sdiff, mem_closedBall, dist_zero_right,
    not_le]
  exact and_comm

/-- **Lemma 2 (Planar Outer Annulus Area):** `volume planarOuterAnnulus = 320 / (81π)`. -/
theorem volume_planarOuterAnnulus :
    volume planarOuterAnnulus = ENNReal.ofReal (320 / (81 * Real.pi)) := by
  have hπ := Real.pi_pos
  have hsub : Metric.closedBall (0 : ℂ) (2 / (9 * Real.pi)) ⊆
      Metric.closedBall 0 (2 / Real.pi) :=
    closedBall_subset_closedBall
      (div_le_div_of_nonneg_left (by norm_num) hπ (by linarith))
  rw [planarOuterAnnulus_eq, measure_sdiff hsub measurableSet_closedBall.nullMeasurableSet
      measure_closedBall_lt_top.ne,
    volume_closedBall_zero_complex (by positivity),
    volume_closedBall_zero_complex (by positivity),
    ← ENNReal.ofReal_sub _ (by positivity)]
  congr 1
  field_simp
  ring

/-- The fundamental mode image covers the closed disk of radius `2 / π` (no retraction). -/
theorem fundamental_disk_covered (F : IsometricFilling M)
    (h_no_retract : ¬ ∃ r : M → Circle2Pi, Continuous r ∧ ∀ θ : Circle2Pi, r (F.ι θ) = θ) :
    Metric.closedBall (0 : ℂ) (2 / Real.pi) ⊆ range (fourierProj 1 ∘ kuratowskiBanach F) :=
  disk_covered_of_no_retraction F (by positivity) _
    ((fourierProj_lipschitzWith 1).continuous.comp (kuratowskiBanach_lipschitzWith F).continuous)
    (fourierProjOneBoundaryHomeomorph F) (fun _ => rfl) h_no_retract

/-- The `0`-th coordinate of `S ∩ bandAnnulus` contains the planar outer annulus. -/
theorem planarOuterAnnulus_subset_image (F : IsometricFilling M)
    (h_no_retract : ¬ ∃ r : M → Circle2Pi, Continuous r ∧ ∀ θ : Circle2Pi, r (F.ι θ) = θ) :
    planarOuterAnnulus ⊆ (fun v : Fin 2 → ℂ => v 0) ''
      (range (oddHarmonicVectorMap 2 ∘ kuratowskiBanach F) ∩ bandAnnulus) := by
  rintro z ⟨hz3, hz1⟩
  obtain ⟨x, hx⟩ := fundamental_disk_covered F h_no_retract
    (mem_closedBall_zero_iff.mpr hz1)
  have h0 : oddHarmonicVectorMap 2 (kuratowskiBanach F x) 0 = z := by
    simpa [oddHarmonicVectorMap] using hx
  refine ⟨oddHarmonicVectorMap 2 (kuratowskiBanach F x), ⟨⟨x, rfl⟩, ?_⟩, h0⟩
  change 2 / (9 * Real.pi) < ‖oddHarmonicVectorMap 2 (kuratowskiBanach F x) 0‖
  rw [h0]
  exact hz3

/-- **Lemma 3 (Outer-Band Area Lower Bound):** under the no-retraction hypothesis,
`320 / (81π) ≤ μH[2] (S ∩ bandAnnulus)` for `S = range (oddHarmonicVectorMap 2 ∘ K_F)`. -/
theorem outer_annulus_hausdorffMeasure_ge (F : IsometricFilling M)
    (h_no_retract : ¬ ∃ r : M → Circle2Pi, Continuous r ∧ ∀ θ : Circle2Pi, r (F.ι θ) = θ) :
    ENNReal.ofReal (320 / (81 * Real.pi)) ≤
      MeasureTheory.Measure.hausdorffMeasure 2
        (range (oddHarmonicVectorMap 2 ∘ kuratowskiBanach F) ∩ bandAnnulus) := by
  calc ENNReal.ofReal (320 / (81 * Real.pi))
      = volume planarOuterAnnulus := volume_planarOuterAnnulus.symm
    _ ≤ MeasureTheory.Measure.hausdorffMeasure 2 planarOuterAnnulus :=
        volume_le_hausdorffMeasure_two_complex _
    _ ≤ MeasureTheory.Measure.hausdorffMeasure 2 ((fun v : Fin 2 → ℂ => v 0) ''
          (range (oddHarmonicVectorMap 2 ∘ kuratowskiBanach F) ∩ bandAnnulus)) :=
        measure_mono (planarOuterAnnulus_subset_image F h_no_retract)
    _ ≤ _ := hausdorffMeasure_image_eval_le _ _

/-- **Theorem 4 (Two-Band Area Bound):** under the no-retraction hypothesis,
`320 / (81π) + μH[2] (S ∩ bandCore) ≤ μH[2] univ`. -/
theorem two_band_area_bound (F : IsometricFilling M)
    (h_no_retract : ¬ ∃ r : M → Circle2Pi, Continuous r ∧ ∀ θ : Circle2Pi, r (F.ι θ) = θ) :
    ENNReal.ofReal (320 / (81 * Real.pi)) +
        MeasureTheory.Measure.hausdorffMeasure 2
          (range (oddHarmonicVectorMap 2 ∘ kuratowskiBanach F) ∩ bandCore) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) := by
  calc _ ≤ MeasureTheory.Measure.hausdorffMeasure 2
          (range (oddHarmonicVectorMap 2 ∘ kuratowskiBanach F) ∩ bandCore) +
        MeasureTheory.Measure.hausdorffMeasure 2
          (range (oddHarmonicVectorMap 2 ∘ kuratowskiBanach F) ∩ bandAnnulus) := by
        rw [add_comm]
        exact add_le_add_right (outer_annulus_hausdorffMeasure_ge F h_no_retract) _
    _ = MeasureTheory.Measure.hausdorffMeasure 2
          (range (oddHarmonicVectorMap 2 ∘ kuratowskiBanach F)) :=
        (hausdorffMeasure_band_decomposition _).symm
    _ ≤ _ := kuratowski_oddHarmonicVectorMap_hausdorffMeasure_le F 2

end

end

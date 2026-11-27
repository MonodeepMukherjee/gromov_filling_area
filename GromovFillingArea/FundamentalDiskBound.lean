/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.BoundaryRadius
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Closed Disk Hausdorff Area & Fundamental-Mode Filling Lower Bound

This file relates `2`-dimensional Hausdorff measure `hausdorffMeasure 2` on `ℂ`
to Lebesgue area (`Complex.volume_closedBall`), proving that any filling whose
fundamental Fourier projection `fourierProj 1 ∘ kuratowskiBanach F` covers the
disk of radius `2 / π` satisfies `4 / π ≤ hausdorffMeasure 2 (univ : Set M)`.
-/

open MeasureTheory Metric Set BoundedContinuousFunction AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The coordinate map `ℂ → (Fin 2 → ℝ)`, `z ↦ ![re z, im z]`, is `1`-Lipschitz from the
Euclidean metric to the sup metric. -/
theorem complex_measurableEquivPi_lipschitz :
    LipschitzWith 1 (Complex.measurableEquivPi : ℂ → (Fin 2 → ℝ)) := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  rw [NNReal.coe_one, one_mul]
  refine (dist_pi_le_iff dist_nonneg).2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · change dist z.re w.re ≤ dist z w
    rw [Real.dist_eq, Complex.dist_eq, ← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  · change dist z.im w.im ≤ dist z w
    rw [Real.dist_eq, Complex.dist_eq, ← Complex.sub_im]
    exact Complex.abs_im_le_norm _

/-- Lebesgue measure on `ℂ` is dominated by the (unnormalized) `2`-dimensional Hausdorff
measure: `volume s ≤ μH[2] s`. (Mathlib's `μH[2]` agrees with `volume` only for the sup
metric on `Fin 2 → ℝ`; on Euclidean `ℂ` it is larger.) -/
theorem volume_le_hausdorffMeasure_two_complex (s : Set ℂ) :
    volume s ≤ MeasureTheory.Measure.hausdorffMeasure 2 s := by
  have h1 : volume s = (volume : Measure (Fin 2 → ℝ)) (Complex.measurableEquivPi '' s) := by
    rw [MeasurableEquiv.image_eq_preimage_symm,
      Complex.volume_preserving_equiv_pi.symm.measure_preimage_equiv]
  have h2 : (volume : Measure (Fin 2 → ℝ)) = MeasureTheory.Measure.hausdorffMeasure 2 := by
    rw [← hausdorffMeasure_pi_real]
    norm_num
  have h3 := complex_measurableEquivPi_lipschitz.hausdorffMeasure_image_le (d := 2)
    (by norm_num) s
  rw [ENNReal.coe_one, ENNReal.one_rpow, one_mul] at h3
  rw [h1, h2]
  exact h3

/-- The Lebesgue area of the closed disk of radius `2 / π` in `ℂ` is `4 / π`. -/
theorem volume_fundamental_disk :
    volume (Metric.closedBall (0 : ℂ) (2 / Real.pi)) = ENNReal.ofReal (4 / Real.pi) := by
  have hπ := Real.pi_pos
  rw [Complex.volume_closedBall, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

/-- **Lemma 1 (Fundamental Harmonic Disk Area in `ℂ`, lower bound):**
The `2`-dimensional Hausdorff measure of the closed disk in `ℂ` of radius
`R₁ = 2 / π` is at least its Lebesgue area `ENNReal.ofReal (4 / π)`.

(An equality `μH[2] (closedBall 0 (2 / π)) = ENNReal.ofReal (4 / π)` would be false:
Mathlib's `hausdorffMeasure` is unnormalized, and on the Euclidean plane it equals
`(4 / π) • volume` classically, giving `16 / π ^ 2`.) -/
theorem hausdorffMeasure_two_fundamental_disk :
    ENNReal.ofReal (4 / Real.pi) ≤
      MeasureTheory.Measure.hausdorffMeasure 2
        (Metric.closedBall (0 : ℂ) (2 / Real.pi)) := by
  rw [← volume_fundamental_disk]
  exact volume_le_hausdorffMeasure_two_complex _

/-- **Lemma 2 (Fundamental-Mode Filling Area Lower Bound `4 / π`):**
If the fundamental Fourier projection `fourierProj 1 ∘ kuratowskiBanach F` fills
the boundary circle of radius `2 / π` (covering `closedBall 0 (2 / π)`), then
`ENNReal.ofReal (4 / π) ≤ hausdorffMeasure 2 (univ : Set M)`. -/
theorem fundamental_mode_filling_area_bound (F : IsometricFilling M)
    (h_fill : Metric.closedBall (0 : ℂ) (2 / Real.pi) ⊆
      range (fourierProj 1 ∘ kuratowskiBanach F)) :
    ENNReal.ofReal (4 / Real.pi) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) :=
  (hausdorffMeasure_two_fundamental_disk.trans (measure_mono h_fill)).trans
    (kuratowski_fourierProj_hausdorffMeasure_le F 1)

end

end

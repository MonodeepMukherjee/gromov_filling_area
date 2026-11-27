/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.FundamentalDiskBound

/-!
# General Odd-Harmonic Disk Area & Multi-Mode Filling Bounds

This file generalizes `FundamentalDiskBound` to every odd harmonic `2 * k + 1`,
proving that the closed disk of radius `R_{2k+1} = 2 / ((2 * k + 1) ^ 2 * π)`
in `ℂ` has `2`-dimensional Hausdorff measure at least `4 / ((2 * k + 1) ^ 4 * π)`,
and deducing the `k`-th odd-mode area bound on any filling covering that disk.
-/

open MeasureTheory Metric Set BoundedContinuousFunction AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The Lebesgue area of the closed disk of radius `2 / ((2k+1)^2 * π)` in `ℂ` is
`4 / ((2k+1)^4 * π)`. -/
theorem volume_odd_disk (k : ℕ) :
    volume (Metric.closedBall (0 : ℂ) (2 / ((2 * (k : ℝ) + 1) ^ 2 * Real.pi))) =
      ENNReal.ofReal (4 / ((2 * (k : ℝ) + 1) ^ 4 * Real.pi)) := by
  have hπ := Real.pi_pos
  have hm : 0 < 2 * (k : ℝ) + 1 := by positivity
  rw [Complex.volume_closedBall, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

/-- **Lemma 1 (General Odd-Harmonic Disk Hausdorff Bound):**
For every `k : ℕ`, the closed disk in `ℂ` of radius `R_{2k+1} = 2 / ((2k+1)^2 * π)`
has `2`-dimensional Hausdorff measure at least `ENNReal.ofReal (4 / ((2k+1)^4 * π))`. -/
theorem hausdorffMeasure_two_odd_disk (k : ℕ) :
    ENNReal.ofReal (4 / ((2 * (k : ℝ) + 1) ^ 4 * Real.pi)) ≤
      MeasureTheory.Measure.hausdorffMeasure 2
        (Metric.closedBall (0 : ℂ) (2 / ((2 * (k : ℝ) + 1) ^ 2 * Real.pi))) := by
  rw [← volume_odd_disk]
  exact volume_le_hausdorffMeasure_two_complex _

/-- **Lemma 2 (`k`-th Odd-Harmonic Filling Area Bound):**
If the `(2 * k + 1)`-th Fourier projection fills its boundary circle of radius
`R_{2k+1}`, then `ENNReal.ofReal (4 / ((2k+1)^4 * π)) ≤ hausdorffMeasure 2 (univ : Set M)`. -/
theorem odd_harmonic_filling_area_bound (F : IsometricFilling M) (k : ℕ)
    (h_fill : Metric.closedBall (0 : ℂ) (2 / ((2 * (k : ℝ) + 1) ^ 2 * Real.pi)) ⊆
      range (fourierProj (2 * (k : ℤ) + 1) ∘ kuratowskiBanach F)) :
    ENNReal.ofReal (4 / ((2 * (k : ℝ) + 1) ^ 4 * Real.pi)) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) :=
  ((hausdorffMeasure_two_odd_disk k).trans (measure_mono h_fill)).trans
    (kuratowski_fourierProj_hausdorffMeasure_le F (2 * (k : ℤ) + 1))

end

end

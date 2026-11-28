/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.CapDeficitIdentity

/-!
# Real-Valued Area Conservation Law & Equivalence to `8 ≤ μH univ`

For any finite-area isometric filling `F : IsometricFilling M` (`μH univ ≠ ⊤`,
`SFinite μH`), this file converts `hausdorffMeasure_eq_two_mul_boundaryBall_add_deficit`
into the exact `ℝ`-valued conservation law:
`(μH univ).toReal = 2 * meanBoundaryBall + 2 * totalCapDeficit`,
proving that `(8 : ENNReal) ≤ μH univ` holds if and only if
`4 ≤ meanBoundaryBall + totalCapDeficit`.
-/

open MeasureTheory Metric Set AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Total `μH`-integrated angular visibility deficit `∫ x, (1/2 - haar(cap_x)).toReal ∂μH`. -/
def totalCapDeficit (F : IsometricFilling M) : ℝ :=
  ∫ x : M, ((1 / 2 : ENNReal) - haarAddCircle (angularCap F x)).toReal
    ∂MeasureTheory.Measure.hausdorffMeasure 2

/-- **Lemma 1 (Exact Real-Valued Area Conservation Law):**
When `μH univ ≠ ⊤` and `SFinite μH` holds, `(μH univ).toReal` equals
`2 * (∫ θ, boundaryBallMeasureReal F θ ∂haarAddCircle) + 2 * totalCapDeficit F`. -/
theorem hausdorffMeasure_toReal_eq_two_mul_add_deficit (F : IsometricFilling M)
    [SFinite (MeasureTheory.Measure.hausdorffMeasure 2 : Measure M)]
    (h_fin : MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) ≠ ⊤) :
    (MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M)).toReal =
      2 * (∫ θ : Circle2Pi, boundaryBallMeasureReal F θ ∂haarAddCircle) +
      2 * totalCapDeficit F := by
  set B := ∫⁻ θ : Circle2Pi,
    MeasureTheory.Measure.hausdorffMeasure 2 (Metric.ball (F.ι θ) (Real.pi / 2))
    ∂haarAddCircle with hB
  set D := ∫⁻ x : M, ((1 / 2 : ENNReal) - haarAddCircle (angularCap F x))
    ∂MeasureTheory.Measure.hausdorffMeasure 2 with hD
  have hid : MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) = 2 * B + 2 * D :=
    hausdorffMeasure_eq_two_mul_boundaryBall_add_deficit F
  have h2B : 2 * B ≠ ⊤ := ne_top_of_le_ne_top h_fin (by rw [hid]; exact le_self_add)
  have h2D : 2 * D ≠ ⊤ := ne_top_of_le_ne_top h_fin (by rw [hid]; exact le_add_self)
  have hBr : (∫ θ : Circle2Pi, boundaryBallMeasureReal F θ ∂haarAddCircle) = B.toReal := by
    have hnn : 0 ≤ᵐ[haarAddCircle] boundaryBallMeasureReal F :=
      ae_of_all _ fun _ => ENNReal.toReal_nonneg
    rw [integral_eq_lintegral_of_nonneg_ae hnn
      (integrable_boundaryBallMeasureReal F h_fin).aestronglyMeasurable]
    congr 1
    exact lintegral_congr fun θ => ENNReal.ofReal_toReal
      (ne_top_of_le_ne_top h_fin (measure_mono (subset_univ _)))
  have hDr : totalCapDeficit F = D.toReal := by
    have hm : Measurable fun x : M =>
        ((1 / 2 : ENNReal) - haarAddCircle (angularCap F x)).toReal :=
      (measurable_const.sub (measurable_haarAddCircle_angularCap F)).ennreal_toReal
    have hnn : 0 ≤ᵐ[MeasureTheory.Measure.hausdorffMeasure 2] fun x : M =>
        ((1 / 2 : ENNReal) - haarAddCircle (angularCap F x)).toReal :=
      ae_of_all _ fun _ => ENNReal.toReal_nonneg
    rw [totalCapDeficit, integral_eq_lintegral_of_nonneg_ae hnn hm.aestronglyMeasurable]
    congr 1
    exact lintegral_congr fun x => ENNReal.ofReal_toReal
      (ne_top_of_le_ne_top (by simp) tsub_le_self)
  rw [hBr, hDr, hid, ENNReal.toReal_add h2B h2D, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat]

/-- **Lemma 2 (Exact Equivalence to Gromov's `8` Lower Bound):**
Under `SFinite μH` and `μH univ ≠ ⊤`, `(8 : ENNReal) ≤ μH univ` holds if and
only if `4 ≤ (∫ θ, boundaryBallMeasureReal F θ ∂haarAddCircle) + totalCapDeficit F`. -/
theorem gromov_eight_iff_mean_ball_add_deficit_ge_four (F : IsometricFilling M)
    [SFinite (MeasureTheory.Measure.hausdorffMeasure 2 : Measure M)]
    (h_fin : MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) ≠ ⊤) :
    (8 : ENNReal) ≤ MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) ↔
      4 ≤ (∫ θ : Circle2Pi, boundaryBallMeasureReal F θ ∂haarAddCircle) +
        totalCapDeficit F := by
  rw [← ENNReal.ofReal_ofNat 8, ENNReal.ofReal_le_iff_le_toReal h_fin,
    hausdorffMeasure_toReal_eq_two_mul_add_deficit F h_fin]
  constructor <;> intro h <;> linarith

end

end

/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.AngularCapExcess

/-!
# Exact Angular-Cap Deficit Identity & Quantitative Area Surplus

Using the Tonelli double-counting identity `lintegral_boundaryBall_eq_lintegral_angularCap`
and the pointwise cap bound `haarAddCircle (angularCap F x) ≤ 1 / 2`, this file proves
the exact `ENNReal` decomposition:
`μH univ = 2 * ∫⁻ θ, μH(B(ι θ, π/2)) dθ`
`  + 2 * ∫⁻ x, (1 / 2 - haarAddCircle (angularCap F x)) dμH`.
Consequently, whenever `4 ≤ mean_θ μH(B(ι θ, π/2))`, any angular visibility deficit
`1 / 2 - haarAddCircle (angularCap F x) > 0` on a set of positive `μH` measure forces
`μH univ` strictly above the conjectured `8` threshold.
-/

open MeasureTheory Metric Set AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- `x ↦ haarAddCircle (angularCap F x)` is measurable (helper). -/
theorem measurable_haarAddCircle_angularCap (F : IsometricFilling M) :
    Measurable fun x : M => haarAddCircle (angularCap F x) := by
  have hcont : Continuous (fun p : M × Circle2Pi => kuratowskiMap F p.1 p.2) :=
    continuous_fst.dist (F.isometry_ι.continuous.comp continuous_snd)
  exact measurable_measure_prodMk_left (isOpen_lt hcont continuous_const).measurableSet

/-- **Lemma 1 (Exact `ENNReal` Area-Deficit Decomposition):**
For every `F : IsometricFilling M` with `SFinite (hausdorffMeasure 2 : Measure M)`,
`hausdorffMeasure 2 (univ : Set M)` equals twice the Haar `lintegral` of boundary
half-ball measures plus twice the `μH`-`lintegral` of the angular cap deficit
`1 / 2 - haarAddCircle (angularCap F x)`. -/
theorem hausdorffMeasure_eq_two_mul_boundaryBall_add_deficit (F : IsometricFilling M)
    [SFinite (MeasureTheory.Measure.hausdorffMeasure 2 : Measure M)] :
    MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) =
      2 * (∫⁻ θ : Circle2Pi,
        MeasureTheory.Measure.hausdorffMeasure 2 (Metric.ball (F.ι θ) (Real.pi / 2))
        ∂haarAddCircle) +
      2 * (∫⁻ x : M, ((1 / 2 : ENNReal) - haarAddCircle (angularCap F x))
        ∂MeasureTheory.Measure.hausdorffMeasure 2) := by
  have hm := measurable_haarAddCircle_angularCap F
  rw [lintegral_boundaryBall_eq_lintegral_angularCap F,
    ← lintegral_const_mul' 2 _ (by simp), ← lintegral_const_mul' 2 _ (by simp),
    ← lintegral_add_left (hm.const_mul 2)]
  have hpt : ∀ x : M, 2 * haarAddCircle (angularCap F x) +
      2 * ((1 / 2 : ENNReal) - haarAddCircle (angularCap F x)) = 1 := fun x => by
    rw [← mul_add, add_tsub_cancel_of_le (haarAddCircle_angularCap_le_half F x), one_div,
      ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]
  simp_rw [hpt]
  exact (lintegral_one).symm

/-- **Lemma 2 (Quantitative Area Surplus Above `8` from Angular Cap Deficit):**
If `SFinite μH` holds and `4 ≤ ∫ θ, boundaryBallMeasureReal F θ ∂haarAddCircle`, then
`(8 : ENNReal) + 2 * ∫⁻ x, (1 / 2 - haarAddCircle (angularCap F x)) ∂μH ≤ μH univ`. -/
theorem gromov_conjecture_excess_of_cap_deficit (F : IsometricFilling M)
    [SFinite (MeasureTheory.Measure.hausdorffMeasure 2 : Measure M)]
    (h_mean : 4 ≤ ∫ θ : Circle2Pi, boundaryBallMeasureReal F θ ∂haarAddCircle) :
    (8 : ENNReal) +
      2 * (∫⁻ x : M, ((1 / 2 : ENNReal) - haarAddCircle (angularCap F x))
        ∂MeasureTheory.Measure.hausdorffMeasure 2) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) := by
  by_cases h_fin : MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) = ⊤
  · rw [h_fin]
    exact le_top
  have hint := integrable_boundaryBallMeasureReal F h_fin
  have hball : ∀ θ : Circle2Pi, ENNReal.ofReal (boundaryBallMeasureReal F θ) =
      MeasureTheory.Measure.hausdorffMeasure 2 (Metric.ball (F.ι θ) (Real.pi / 2)) :=
    fun θ => ENNReal.ofReal_toReal (ne_top_of_le_ne_top h_fin (measure_mono (subset_univ _)))
  have h4 : (4 : ENNReal) ≤ ∫⁻ θ : Circle2Pi,
      MeasureTheory.Measure.hausdorffMeasure 2 (Metric.ball (F.ι θ) (Real.pi / 2))
      ∂haarAddCircle := by
    calc (4 : ENNReal) = ENNReal.ofReal 4 := (ENNReal.ofReal_ofNat 4).symm
      _ ≤ ENNReal.ofReal (∫ θ : Circle2Pi, boundaryBallMeasureReal F θ ∂haarAddCircle) :=
        ENNReal.ofReal_le_ofReal h_mean
      _ = ∫⁻ θ : Circle2Pi, ENNReal.ofReal (boundaryBallMeasureReal F θ) ∂haarAddCircle :=
        ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => ENNReal.toReal_nonneg)
      _ = _ := lintegral_congr hball
  have h8 : (8 : ENNReal) ≤ 2 * ∫⁻ θ : Circle2Pi,
      MeasureTheory.Measure.hausdorffMeasure 2 (Metric.ball (F.ι θ) (Real.pi / 2))
      ∂haarAddCircle := by
    calc (8 : ENNReal) = 2 * 4 := by norm_num
      _ ≤ _ := by gcongr
  rw [hausdorffMeasure_eq_two_mul_boundaryBall_add_deficit F]
  exact add_le_add h8 le_rfl

end

end

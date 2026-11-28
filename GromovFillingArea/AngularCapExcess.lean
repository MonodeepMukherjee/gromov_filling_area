/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.IncidenceFubini

/-!
# Incidence Half-Area Bound, Automatic Integrability & Boundary Cap `1 / 2`

This file combines the two lemmas of `IncidenceFubini` to prove:
1. `∫⁻ θ, μH (ball (F.ι θ) (π / 2)) ∂haarAddCircle ≤ (1 / 2) * μH univ`
   (which automatically implies `Integrable (boundaryBallMeasureReal F) haarAddCircle`
   whenever `μH univ ≠ ⊤`, discharging the integrability hypothesis in `AveragedBallBound`).
2. At every boundary point `x = F.ι θ₀`, the open angular cap `angularCap F (F.ι θ₀)`
   has exact Haar measure `1 / 2` (`haarAddCircle (angularCap F (F.ι θ₀)) = 1 / 2`).
-/

open MeasureTheory Metric Set AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Lemma 1 (Combined Incidence Half-Area Bound):**
For every `F : IsometricFilling M` with `SFinite (hausdorffMeasure 2 : Measure M)`,
the Haar `lintegral` of boundary half-ball measures is at most `(1 / 2) * μH univ`. -/
theorem lintegral_boundaryBall_le_half_area (F : IsometricFilling M)
    [SFinite (MeasureTheory.Measure.hausdorffMeasure 2 : Measure M)] :
    (∫⁻ θ : Circle2Pi,
      MeasureTheory.Measure.hausdorffMeasure 2 (Metric.ball (F.ι θ) (Real.pi / 2))
      ∂haarAddCircle) ≤
    (1 / 2 : ENNReal) * MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) := by
  rw [lintegral_boundaryBall_eq_lintegral_angularCap F]
  calc (∫⁻ x : M, haarAddCircle (angularCap F x) ∂MeasureTheory.Measure.hausdorffMeasure 2)
      ≤ ∫⁻ _ : M, (1 / 2 : ENNReal) ∂MeasureTheory.Measure.hausdorffMeasure 2 :=
        lintegral_mono (haarAddCircle_angularCap_le_half F)
    _ = _ := lintegral_const _

/-- `θ ↦ μH (ball (F.ι θ) (π / 2))` is measurable when `μH` is s-finite (helper). -/
theorem measurable_hausdorffMeasure_boundaryBall (F : IsometricFilling M)
    [SFinite (MeasureTheory.Measure.hausdorffMeasure 2 : Measure M)] :
    Measurable fun θ : Circle2Pi =>
      MeasureTheory.Measure.hausdorffMeasure 2 (Metric.ball (F.ι θ) (Real.pi / 2)) := by
  have hcont : Continuous (fun p : M × Circle2Pi => dist p.1 (F.ι p.2)) :=
    continuous_fst.dist (F.isometry_ι.continuous.comp continuous_snd)
  exact measurable_measure_prodMk_right (isOpen_lt hcont continuous_const).measurableSet

/-- **Lemma 3 (Automatic Integrability):** if `μH` is s-finite and `μH univ ≠ ⊤`, then
`boundaryBallMeasureReal F` is integrable for the normalized Haar measure. -/
theorem integrable_boundaryBallMeasureReal (F : IsometricFilling M)
    [SFinite (MeasureTheory.Measure.hausdorffMeasure 2 : Measure M)]
    (h_fin : MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) ≠ ⊤) :
    Integrable (boundaryBallMeasureReal F) haarAddCircle :=
  integrable_toReal_of_lintegral_ne_top
    (measurable_hausdorffMeasure_boundaryBall F).aemeasurable
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) h_fin)
      (lintegral_boundaryBall_le_half_area F))

/-- **Corollary (Reduction without `h_int`):** if `μH` is s-finite and the Haar-averaged
boundary half-ball measure is at least `4`, then `8 ≤ μH univ`. -/
theorem gromov_conjecture_of_mean_boundaryBall_ge_four_of_sFinite (F : IsometricFilling M)
    [SFinite (MeasureTheory.Measure.hausdorffMeasure 2 : Measure M)]
    (h_mean : 4 ≤ ∫ θ : Circle2Pi, boundaryBallMeasureReal F θ ∂haarAddCircle) :
    (8 : ENNReal) ≤ MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) := by
  by_cases h_fin : MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) = ⊤
  · rw [h_fin]
    exact le_top
  · exact gromov_conjecture_of_mean_boundaryBall_ge_four F
      (integrable_boundaryBallMeasureReal F h_fin) h_mean

/-- On `Circle2Pi`, the angles at distance exactly `π / 2` from `θ₀` are `θ₀ ∓ π / 2`
(helper). -/
theorem circle2Pi_eq_of_dist_eq_half_pi {θ₀ θ : Circle2Pi} (h : dist θ₀ θ = Real.pi / 2) :
    θ = θ₀ - ((Real.pi / 2 : ℝ) : Circle2Pi) ∨ θ = θ₀ + ((Real.pi / 2 : ℝ) : Circle2Pi) := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective (θ₀ - θ)
  set t := s - round ((2 * Real.pi)⁻¹ * s) * (2 * Real.pi) with ht
  have hts : ((t : ℝ) : Circle2Pi) = θ₀ - θ := by
    rw [← hs]
    have : ((t - s : ℝ) : Circle2Pi) = 0 :=
      (AddCircle.coe_eq_zero_iff _).2 ⟨-round ((2 * Real.pi)⁻¹ * s), by
        rw [ht, zsmul_eq_mul]; push_cast; ring⟩
    rw [AddCircle.coe_sub, sub_eq_zero] at this
    exact this
  have hn : |t| = Real.pi / 2 := by
    rw [dist_eq_norm, ← hs, AddCircle.norm_eq] at h
    exact h
  rcases abs_eq (by positivity) |>.1 hn with h1 | h1
  · left
    rw [← h1, hts]
    abel
  · right
    rw [show (Real.pi / 2 : ℝ) = -t by linarith, AddCircle.coe_neg, hts]
    abel

/-- **Lemma 2 (Exact Boundary Angular Cap Measure `1 / 2`):**
At every boundary point `F.ι θ₀`, `haarAddCircle (angularCap F (F.ι θ₀)) = 1 / 2`. -/
theorem haarAddCircle_angularCap_boundary_eq_half (F : IsometricFilling M) (θ₀ : Circle2Pi) :
    haarAddCircle (angularCap F (F.ι θ₀)) = 1 / 2 := by
  refine le_antisymm (haarAddCircle_angularCap_le_half F (F.ι θ₀)) ?_
  set C := angularCap F (F.ι θ₀) with hCdef
  set C' := (fun θ => θ + (Real.pi : Circle2Pi)) ⁻¹' C with hC'def
  have hsub : (C ∪ C')ᶜ ⊆
      ({θ₀ - ((Real.pi / 2 : ℝ) : Circle2Pi), θ₀ + ((Real.pi / 2 : ℝ) : Circle2Pi)} :
        Set Circle2Pi) := by
    intro θ hθ
    rw [mem_compl_iff, mem_union, not_or] at hθ
    have h1 : Real.pi / 2 ≤ dist θ₀ θ := by
      rw [← kuratowskiMap_boundary F]
      exact not_lt.1 hθ.1
    have h2 : Real.pi / 2 ≤ dist θ₀ (θ + (Real.pi : Circle2Pi)) := by
      rw [← kuratowskiMap_boundary F]
      exact not_lt.1 hθ.2
    have hsum := circle2Pi_dist_add_antipodal θ₀ θ
    exact circle2Pi_eq_of_dist_eq_half_pi (by linarith)
  have hzero : haarAddCircle (C ∪ C')ᶜ = 0 :=
    measure_mono_null hsub ((Set.toFinite _).measure_zero haarAddCircle)
  have heq : haarAddCircle C' = haarAddCircle C := measure_preimage_add_right _ _ _
  refine ENNReal.div_le_of_le_mul ?_
  calc (1 : ENNReal) = haarAddCircle (univ : Set Circle2Pi) := measure_univ.symm
    _ = haarAddCircle ((C ∪ C') ∪ (C ∪ C')ᶜ) := by rw [union_compl_self]
    _ ≤ haarAddCircle (C ∪ C') + haarAddCircle (C ∪ C')ᶜ := measure_union_le _ _
    _ ≤ haarAddCircle C + haarAddCircle C' + 0 := by
        rw [hzero]
        exact add_le_add (measure_union_le C C') le_rfl
    _ = haarAddCircle C * 2 := by rw [add_zero, heq, mul_two]

end

end

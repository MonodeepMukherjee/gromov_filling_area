/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.AveragedBallBound

/-!
# Incidence Set Double-Counting & Angular Cap Measure Bounds

This file defines the angular visibility cap `angularCap F x := {θ | kuratowskiMap F x θ < π / 2}`
for `x : M`, proves that `angularCap F x` is open and satisfies
`haarAddCircle (angularCap F x) ≤ 1 / 2` (via antipodal disjointness on `Circle2Pi`),
and proves the exact Tonelli / Fubini double-counting identity equating the
Haar-averaged boundary half-ball `μH` measure to the `μH`-integral of
`haarAddCircle (angularCap F x)`.
-/

open MeasureTheory Metric Set AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The open angular visibility cap `{θ : Circle2Pi | dist x (F.ι θ) < π / 2}` seen from `x : M`. -/
def angularCap (F : IsometricFilling M) (x : M) : Set Circle2Pi :=
  {θ : Circle2Pi | kuratowskiMap F x θ < Real.pi / 2}

/-- `angularCap F x` is open in `Circle2Pi`. -/
theorem isOpen_angularCap (F : IsometricFilling M) (x : M) : IsOpen (angularCap F x) :=
  isOpen_lt (kuratowskiMap_lipschitzWith F x).continuous continuous_const

/-- **Lemma 1 (Openness & Half-Circle Measure Cap of `angularCap F x`):**
For every `x : M`, `angularCap F x` is open in `Circle2Pi` and has normalized
Haar measure at most `1 / 2` (`haarAddCircle (angularCap F x) ≤ 1 / 2`). -/
theorem haarAddCircle_angularCap_le_half (F : IsometricFilling M) (x : M) :
    haarAddCircle (angularCap F x) ≤ 1 / 2 := by
  set S := angularCap F x with hSdef
  have hS : MeasurableSet S := (isOpen_angularCap F x).measurableSet
  have hdisj : Disjoint S ((fun θ => θ + (Real.pi : Circle2Pi)) ⁻¹' S) := by
    rw [Set.disjoint_left]
    intro θ h₁ h₂
    have hsum := kuratowski_antipodal_sum F x θ
    rw [circle2Pi_dist_add_pi] at hsum
    simp only [hSdef, angularCap, mem_preimage, mem_ofPred_eq] at h₁ h₂
    linarith
  have heq : haarAddCircle ((fun θ => θ + (Real.pi : Circle2Pi)) ⁻¹' S) = haarAddCircle S :=
    measure_preimage_add_right _ _ _
  have h2 : haarAddCircle S + haarAddCircle S ≤ 1 := by
    calc haarAddCircle S + haarAddCircle S
        = haarAddCircle (S ∪ (fun θ => θ + (Real.pi : Circle2Pi)) ⁻¹' S) := by
          rw [measure_union hdisj (hS.preimage (measurable_add_const _)), heq]
      _ ≤ haarAddCircle (univ : Set Circle2Pi) := measure_mono (subset_univ _)
      _ = 1 := measure_univ
  rw [ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), mul_two]
  exact h2

/-- **Lemma 2 (Tonelli Double-Counting Identity for Boundary Half-Balls):**
Assuming `SFinite` on `hausdorffMeasure 2`, the `lintegral` over `Circle2Pi` of
`hausdorffMeasure 2 (Metric.ball (F.ι θ) (π / 2))` equals the `lintegral` over `M`
of `haarAddCircle (angularCap F x)`. -/
theorem lintegral_boundaryBall_eq_lintegral_angularCap (F : IsometricFilling M)
    [SFinite (MeasureTheory.Measure.hausdorffMeasure 2 : Measure M)] :
    (∫⁻ θ : Circle2Pi,
      MeasureTheory.Measure.hausdorffMeasure 2 (Metric.ball (F.ι θ) (Real.pi / 2))
      ∂haarAddCircle) =
    (∫⁻ x : M, haarAddCircle (angularCap F x)
      ∂MeasureTheory.Measure.hausdorffMeasure 2) := by
  set E : Set (M × Circle2Pi) := {p | kuratowskiMap F p.1 p.2 < Real.pi / 2} with hEdef
  have hcont : Continuous (fun p : M × Circle2Pi => kuratowskiMap F p.1 p.2) :=
    continuous_fst.dist (F.isometry_ι.continuous.comp continuous_snd)
  have hE : MeasurableSet E := (isOpen_lt hcont continuous_const).measurableSet
  have hf : Measurable (E.indicator (1 : M × Circle2Pi → ENNReal)) :=
    measurable_const.indicator hE
  calc (∫⁻ θ : Circle2Pi,
        MeasureTheory.Measure.hausdorffMeasure 2 (Metric.ball (F.ι θ) (Real.pi / 2))
        ∂haarAddCircle)
      = ∫⁻ θ : Circle2Pi, ∫⁻ x : M, E.indicator 1 (x, θ)
          ∂MeasureTheory.Measure.hausdorffMeasure 2 ∂haarAddCircle := by
        refine lintegral_congr fun θ => ?_
        rw [← lintegral_indicator_one Metric.isOpen_ball.measurableSet]
        rfl
    _ = ∫⁻ x : M, ∫⁻ θ : Circle2Pi, E.indicator 1 (x, θ)
          ∂haarAddCircle ∂MeasureTheory.Measure.hausdorffMeasure 2 :=
        (lintegral_lintegral_swap (f := fun (x : M) (θ : Circle2Pi) => E.indicator 1 (x, θ))
          hf.aemeasurable).symm
    _ = _ := by
        refine lintegral_congr fun x => ?_
        rw [← lintegral_indicator_one (isOpen_angularCap F x).measurableSet]
        rfl

end

end

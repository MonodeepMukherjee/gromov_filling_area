/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.QuarterCircleSquare

/-!
# `L¹`-Diamond Area (`π² / 2`) & Boundary Embedding Injectivity

This file computes the `2`-dimensional Hausdorff measure (`hausdorffMeasure 2`)
of the `L¹`-diamond `quarterDiamond = {p : Fin 2 → ℝ | |p 0 - π/2| + |p 1 - π/2| ≤ π/2}`
in the sup-norm plane (`ENNReal.ofReal (Real.pi ^ 2 / 2)` via `hausdorffMeasure_pi_real`),
and proves that `quarterPairMap F ∘ F.ι` injects `Circle2Pi` onto the diamond boundary.
-/

open MeasureTheory Metric Set BoundedContinuousFunction AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The closed `L¹`-diamond of radius `π / 2` centered at `(π / 2, π / 2)` in `Fin 2 → ℝ`. -/
def quarterDiamond : Set (Fin 2 → ℝ) :=
  {p | |p 0 - Real.pi / 2| + |p 1 - Real.pi / 2| ≤ Real.pi / 2}

/-- The boundary of `quarterDiamond` in `Fin 2 → ℝ`. -/
def quarterDiamondBoundary : Set (Fin 2 → ℝ) :=
  {p | |p 0 - Real.pi / 2| + |p 1 - Real.pi / 2| = Real.pi / 2}

/-- `dist t (π/2) = t + 3π/2` for a representative `t ∈ (-π, -π/2]`. -/
theorem dist_coe_halfPi_of_le_neg {t : ℝ} (h1 : -Real.pi < t) (h2 : t ≤ -(Real.pi / 2)) :
    dist (t : Circle2Pi) ((Real.pi / 2 : ℝ) : Circle2Pi) = t + 3 * Real.pi / 2 := by
  rw [dist_eq_norm, ← AddCircle.coe_sub,
    ← AddCircle.coe_add_period (p := 2 * Real.pi) (t - Real.pi / 2),
    circle2Pi_norm_coe_of_abs_le _ (abs_le.2 ⟨by linarith, by linarith⟩),
    abs_of_pos (by linarith [Real.pi_pos])]
  ring

/-- `dist t (π/2) = π/2 - t` for a representative `t ∈ [-π/2, π/2]`. -/
theorem dist_coe_halfPi_of_abs_le {t : ℝ} (h1 : -(Real.pi / 2) ≤ t) (h2 : t ≤ Real.pi / 2) :
    dist (t : Circle2Pi) ((Real.pi / 2 : ℝ) : Circle2Pi) = Real.pi / 2 - t := by
  rw [dist_eq_norm, ← AddCircle.coe_sub,
    circle2Pi_norm_coe_of_abs_le _ (abs_le.2 ⟨by linarith, by linarith⟩),
    abs_of_nonpos (by linarith)]
  ring

/-- `dist t (π/2) = t - π/2` for a representative `t ∈ [π/2, π]`. -/
theorem dist_coe_halfPi_of_ge {t : ℝ} (h1 : Real.pi / 2 ≤ t) (h2 : t ≤ Real.pi) :
    dist (t : Circle2Pi) ((Real.pi / 2 : ℝ) : Circle2Pi) = t - Real.pi / 2 := by
  rw [dist_eq_norm, ← AddCircle.coe_sub,
    circle2Pi_norm_coe_of_abs_le _ (abs_le.2 ⟨by linarith, by linarith⟩),
    abs_of_nonneg (by linarith)]

/-- `|a| + |b| ≤ r ↔ |a + b| ≤ r ∧ |a - b| ≤ r`: the `L¹` ball is a rotated `L^∞` ball. -/
theorem abs_add_abs_le_iff (a b r : ℝ) :
    |a| + |b| ≤ r ↔ |a + b| ≤ r ∧ |a - b| ≤ r := by
  constructor
  · intro h
    constructor <;> rw [abs_le] <;> constructor <;>
      linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b]
  · rintro ⟨h1, h2⟩
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb <;>
      simp only [abs_of_nonneg, abs_of_nonpos, ha, hb] <;> linarith

/-- The shear `(a, b) ↦ (a + b, a - b)` on `Fin 2 → ℝ`, of determinant `-2`. -/
def quarterShear : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  Matrix.toLin' !![1, 1; 1, -1]

theorem quarterShear_apply_zero (v : Fin 2 → ℝ) : quarterShear v 0 = v 0 + v 1 := by
  simp [quarterShear, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem quarterShear_apply_one (v : Fin 2 → ℝ) : quarterShear v 1 = v 0 - v 1 := by
  simp [quarterShear, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

theorem det_quarterShear : LinearMap.det quarterShear = -2 := by
  rw [quarterShear, LinearMap.det_toLin', Matrix.det_fin_two_of]
  norm_num

/-- The diamond is the preimage of the box `[-π/2, π/2]²` under `p ↦ shear (p - c)`,
with centre `c = (π/2, π/2)`. -/
theorem quarterDiamond_eq_preimage :
    quarterDiamond = (fun p => p + -(fun _ => Real.pi / 2 : Fin 2 → ℝ)) ⁻¹'
      (quarterShear ⁻¹' Icc (fun _ => -(Real.pi / 2)) (fun _ => Real.pi / 2)) := by
  ext p
  simp only [quarterDiamond, mem_ofPred_eq, mem_preimage, mem_Icc, Pi.le_def,
    Fin.forall_fin_two, quarterShear_apply_zero, quarterShear_apply_one, Pi.add_apply,
    Pi.neg_apply]
  rw [← sub_eq_add_neg, ← sub_eq_add_neg, abs_add_abs_le_iff, abs_le, abs_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, h3⟩, h2, h4⟩
  · rintro ⟨⟨h1, h3⟩, h2, h4⟩
    exact ⟨⟨h1, h2⟩, h3, h4⟩

/-- **Lemma 1 (Boundary Injectivity onto `quarterDiamondBoundary`):**
The map `θ ↦ quarterPairMap F (F.ι θ)` is injective on `Circle2Pi` and lands in
`quarterDiamondBoundary`. -/
theorem quarterPairMap_boundary_injective (F : IsometricFilling M) :
    Function.Injective (fun θ : Circle2Pi => quarterPairMap F (F.ι θ)) := by
  have hπ := Real.pi_pos
  intro θ₁ θ₂ h
  have h0 : dist θ₁ 0 = dist θ₂ 0 := by
    have := congrFun h 0
    change kuratowskiMap F (F.ι θ₁) 0 = kuratowskiMap F (F.ι θ₂) 0 at this
    rwa [kuratowskiMap_boundary, kuratowskiMap_boundary] at this
  have h1 : dist θ₁ ((Real.pi / 2 : ℝ) : Circle2Pi) =
      dist θ₂ ((Real.pi / 2 : ℝ) : Circle2Pi) := by
    have := congrFun h 1
    change kuratowskiMap F (F.ι θ₁) ((Real.pi / 2 : ℝ) : Circle2Pi) =
      kuratowskiMap F (F.ι θ₂) ((Real.pi / 2 : ℝ) : Circle2Pi) at this
    rwa [kuratowskiMap_boundary, kuratowskiMap_boundary] at this
  obtain ⟨t₁, ⟨a₁, b₁⟩, rfl⟩ := circle2Pi_exists_rep_Ioc θ₁
  obtain ⟨t₂, ⟨a₂, b₂⟩, rfl⟩ := circle2Pi_exists_rep_Ioc θ₂
  have hu : ∀ t : ℝ, -Real.pi < t → t ≤ Real.pi → dist (t : Circle2Pi) 0 = |t| :=
    fun t ha hb => by
      rw [dist_zero_right, circle2Pi_norm_coe_of_abs_le t (abs_le.2 ⟨by linarith, hb⟩)]
  rw [hu t₁ a₁ b₁, hu t₂ a₂ b₂] at h0
  suffices t₁ = t₂ by rw [this]
  -- equal distances to `0`: `t₁ = ± t₂`; distances to `π/2` rule out `t₁ = -t₂ ≠ t₂`
  rcases abs_eq_abs.mp h0 with h | h
  · exact h
  rcases le_or_gt t₂ (-(Real.pi / 2)) with c₁ | c₁
  · rw [dist_coe_halfPi_of_ge (by linarith) b₁, dist_coe_halfPi_of_le_neg a₂ c₁] at h1
    linarith
  rcases le_or_gt t₂ (Real.pi / 2) with c₂ | c₂
  · rw [dist_coe_halfPi_of_abs_le (by linarith) (by linarith),
      dist_coe_halfPi_of_abs_le c₁.le c₂] at h1
    linarith
  · rw [dist_coe_halfPi_of_le_neg a₁ (by linarith), dist_coe_halfPi_of_ge c₂.le b₂] at h1
    linarith

/-- **Lemma 2 (Exact `2`-Dimensional Hausdorff Area `π² / 2` of `quarterDiamond`):**
In the sup-norm plane `Fin 2 → ℝ`, `hausdorffMeasure 2 quarterDiamond` equals
`ENNReal.ofReal (Real.pi ^ 2 / 2)`. -/
theorem hausdorffMeasure_two_quarterDiamond :
    MeasureTheory.Measure.hausdorffMeasure 2 quarterDiamond =
      ENNReal.ofReal (Real.pi ^ 2 / 2) := by
  have hπ := Real.pi_pos
  have hvol : (volume : Measure (Fin 2 → ℝ)) = MeasureTheory.Measure.hausdorffMeasure 2 := by
    rw [← hausdorffMeasure_pi_real]
    norm_num
  rw [← hvol, quarterDiamond_eq_preimage, measure_preimage_add_right,
    MeasureTheory.Measure.addHaar_preimage_linearMap _ (by rw [det_quarterShear]; norm_num),
    det_quarterShear, Real.volume_Icc_pi, Fin.prod_univ_two,
    ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [abs_of_neg (by norm_num)]
  ring

end

end

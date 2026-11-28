/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.DiamondAreaBound

/-!
# Three Equidistant Anchors: the `L^∞_3` Boundary Map

The map `x ↦ (d(x, ι 0), d(x, ι (2π/3)), d(x, ι (4π/3)))` into the sup-norm space
`Fin 3 → ℝ` is `1`-Lipschitz, injective on the boundary, and sends the boundary point `θ`
to sup-distance `π / 3 + |ψ - π / 6|` from the centre `(π/2, π/2, π/2)`, where `ψ` is the
distance from `θ` to the nearest anchor. This is groundwork for three-point filling
arguments (`scripts/linf_multi_point_search.py`); it does not by itself give an area bound,
since a lower bound for fillings of a curve in `L^∞_3` is not formalized.
-/

open MeasureTheory Metric Set BoundedContinuousFunction AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The three-anchor Kuratowski map `x ↦ ![f_x(0), f_x(2π/3), f_x(4π/3)]`. -/
def threePointMap (F : IsometricFilling M) (x : M) : Fin 3 → ℝ :=
  ![kuratowskiMap F x 0, kuratowskiMap F x ((2 * Real.pi / 3 : ℝ) : Circle2Pi),
    kuratowskiMap F x ((4 * Real.pi / 3 : ℝ) : Circle2Pi)]

/-- The centre `(π/2, π/2, π/2)` of the boundary image. -/
def threeCenter : Fin 3 → ℝ :=
  ![Real.pi / 2, Real.pi / 2, Real.pi / 2]

/-- **`threePointMap F` is `1`-Lipschitz into the sup-norm space `Fin 3 → ℝ`.** -/
theorem threePointMap_lipschitzWith (F : IsometricFilling M) :
    LipschitzWith 1 (threePointMap F) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul]
  refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
  fin_cases i
  · change dist (kuratowskiMap F x 0) (kuratowskiMap F y 0) ≤ dist x y
    rw [Real.dist_eq]
    exact kuratowski_nonexpansive F x y 0
  · change dist (kuratowskiMap F x ((2 * Real.pi / 3 : ℝ) : Circle2Pi))
      (kuratowskiMap F y ((2 * Real.pi / 3 : ℝ) : Circle2Pi)) ≤ dist x y
    rw [Real.dist_eq]
    exact kuratowski_nonexpansive F x y _
  · change dist (kuratowskiMap F x ((4 * Real.pi / 3 : ℝ) : Circle2Pi))
      (kuratowskiMap F y ((4 * Real.pi / 3 : ℝ) : Circle2Pi)) ≤ dist x y
    rw [Real.dist_eq]
    exact kuratowski_nonexpansive F x y _

/-- So `μH[2]` of the image is at most `μH[2] (univ : Set M)`. -/
theorem threePointMap_hausdorffMeasure_le (F : IsometricFilling M) :
    MeasureTheory.Measure.hausdorffMeasure 2 (range (threePointMap F)) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) := by
  have h := (threePointMap_lipschitzWith F).hausdorffMeasure_image_le (d := 2) (by norm_num)
    (univ : Set M)
  rwa [image_univ, ENNReal.coe_one, ENNReal.one_rpow, one_mul] at h

/-! ### Distances from a representative `t ∈ (-π, π]` to the anchors -/

theorem dist_coe_zero_of_abs_le {t : ℝ} (h : |t| ≤ Real.pi) :
    dist (t : Circle2Pi) 0 = |t| := by
  rw [dist_zero_right, circle2Pi_norm_coe_of_abs_le t h]

theorem dist_coe_twoThirds_of_le {t : ℝ} (h1 : -Real.pi < t) (h2 : t ≤ -(Real.pi / 3)) :
    dist (t : Circle2Pi) ((2 * Real.pi / 3 : ℝ) : Circle2Pi) = t + 4 * Real.pi / 3 := by
  rw [dist_eq_norm, ← AddCircle.coe_sub,
    ← AddCircle.coe_add_period (p := 2 * Real.pi) (t - 2 * Real.pi / 3),
    circle2Pi_norm_coe_of_abs_le _ (abs_le.2 ⟨by linarith, by linarith⟩),
    abs_of_nonneg (by linarith)]
  ring

theorem dist_coe_twoThirds_of_mem {t : ℝ} (h1 : -(Real.pi / 3) ≤ t)
    (h2 : t ≤ 2 * Real.pi / 3) :
    dist (t : Circle2Pi) ((2 * Real.pi / 3 : ℝ) : Circle2Pi) = 2 * Real.pi / 3 - t := by
  rw [dist_eq_norm, ← AddCircle.coe_sub,
    circle2Pi_norm_coe_of_abs_le _ (abs_le.2 ⟨by linarith, by linarith⟩),
    abs_of_nonpos (by linarith)]
  ring

theorem dist_coe_twoThirds_of_ge {t : ℝ} (h1 : 2 * Real.pi / 3 ≤ t) (h2 : t ≤ Real.pi) :
    dist (t : Circle2Pi) ((2 * Real.pi / 3 : ℝ) : Circle2Pi) = t - 2 * Real.pi / 3 := by
  rw [dist_eq_norm, ← AddCircle.coe_sub,
    circle2Pi_norm_coe_of_abs_le _ (abs_le.2 ⟨by linarith, by linarith⟩),
    abs_of_nonneg (by linarith)]

theorem dist_coe_fourThirds_of_le {t : ℝ} (h1 : -Real.pi < t)
    (h2 : t ≤ -(2 * Real.pi / 3)) :
    dist (t : Circle2Pi) ((4 * Real.pi / 3 : ℝ) : Circle2Pi) = -t - 2 * Real.pi / 3 := by
  rw [dist_eq_norm, ← AddCircle.coe_sub,
    ← AddCircle.coe_add_period (p := 2 * Real.pi) (t - 4 * Real.pi / 3),
    circle2Pi_norm_coe_of_abs_le _ (abs_le.2 ⟨by linarith, by linarith⟩),
    abs_of_nonpos (by linarith)]
  ring

theorem dist_coe_fourThirds_of_mem {t : ℝ} (h1 : -(2 * Real.pi / 3) ≤ t)
    (h2 : t ≤ Real.pi / 3) :
    dist (t : Circle2Pi) ((4 * Real.pi / 3 : ℝ) : Circle2Pi) = t + 2 * Real.pi / 3 := by
  rw [dist_eq_norm, ← AddCircle.coe_sub,
    ← AddCircle.coe_add_period (p := 2 * Real.pi) (t - 4 * Real.pi / 3),
    circle2Pi_norm_coe_of_abs_le _ (abs_le.2 ⟨by linarith, by linarith⟩),
    abs_of_nonneg (by linarith)]
  ring

theorem dist_coe_fourThirds_of_ge {t : ℝ} (h1 : Real.pi / 3 ≤ t) (h2 : t ≤ Real.pi) :
    dist (t : Circle2Pi) ((4 * Real.pi / 3 : ℝ) : Circle2Pi) = 4 * Real.pi / 3 - t := by
  rw [dist_eq_norm, ← AddCircle.coe_sub,
    circle2Pi_norm_coe_of_abs_le _ (abs_le.2 ⟨by linarith, by linarith⟩),
    abs_of_nonpos (by linarith)]
  ring

/-- On the boundary, `threePointMap F (F.ι θ) = ![d(θ, 0), d(θ, 2π/3), d(θ, 4π/3)]`. -/
theorem threePointMap_boundary_apply (F : IsometricFilling M) (θ : Circle2Pi) :
    threePointMap F (F.ι θ) = ![dist θ 0, dist θ ((2 * Real.pi / 3 : ℝ) : Circle2Pi),
      dist θ ((4 * Real.pi / 3 : ℝ) : Circle2Pi)] := by
  rw [threePointMap, kuratowskiMap_boundary, kuratowskiMap_boundary, kuratowskiMap_boundary]

/-- **Boundary injectivity.** Equal distances to `0` give `t₁ = ± t₂`; equal distances to
`2π/3` rule out `t₁ = -t₂ ≠ t₂`. -/
theorem threePointMap_boundary_injective (F : IsometricFilling M) :
    Function.Injective (fun θ : Circle2Pi => threePointMap F (F.ι θ)) := by
  have hπ := Real.pi_pos
  intro θ₁ θ₂ h
  have h' : threePointMap F (F.ι θ₁) = threePointMap F (F.ι θ₂) := h
  rw [threePointMap_boundary_apply, threePointMap_boundary_apply] at h'
  have h0 : dist θ₁ 0 = dist θ₂ 0 := congrFun h' 0
  have h1 : dist θ₁ ((2 * Real.pi / 3 : ℝ) : Circle2Pi) =
      dist θ₂ ((2 * Real.pi / 3 : ℝ) : Circle2Pi) := congrFun h' 1
  obtain ⟨t₁, ⟨a₁, b₁⟩, rfl⟩ := circle2Pi_exists_rep_Ioc θ₁
  obtain ⟨t₂, ⟨a₂, b₂⟩, rfl⟩ := circle2Pi_exists_rep_Ioc θ₂
  rw [dist_coe_zero_of_abs_le (abs_le.2 ⟨by linarith, b₁⟩),
    dist_coe_zero_of_abs_le (abs_le.2 ⟨by linarith, b₂⟩)] at h0
  suffices t₁ = t₂ by rw [this]
  rcases abs_eq_abs.mp h0 with h | h
  · exact h
  rcases le_or_gt t₂ (-(2 * Real.pi / 3)) with c₁ | c₁
  · rw [dist_coe_twoThirds_of_ge (by linarith) b₁,
      dist_coe_twoThirds_of_le a₂ (by linarith)] at h1
    linarith
  rcases le_or_gt t₂ (-(Real.pi / 3)) with c₂ | c₂
  · rw [dist_coe_twoThirds_of_mem (by linarith) (by linarith),
      dist_coe_twoThirds_of_le a₂ c₂] at h1
    linarith
  rcases le_or_gt t₂ (Real.pi / 3) with c₃ | c₃
  · rw [dist_coe_twoThirds_of_mem (by linarith) (by linarith),
      dist_coe_twoThirds_of_mem c₂.le (by linarith)] at h1
    linarith
  rcases le_or_gt t₂ (2 * Real.pi / 3) with c₄ | c₄
  · rw [dist_coe_twoThirds_of_le a₁ (by linarith),
      dist_coe_twoThirds_of_mem (by linarith) c₄] at h1
    linarith
  · rw [dist_coe_twoThirds_of_le a₁ (by linarith),
      dist_coe_twoThirds_of_ge c₄.le b₂] at h1
    linarith

/-- The sup-distance from the centre to `![a, b, c]`. -/
theorem dist_threeCenter (a b c : ℝ) :
    dist threeCenter ![a, b, c] =
      max (max |a - Real.pi / 2| |b - Real.pi / 2|) |c - Real.pi / 2| := by
  apply le_antisymm
  · refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
    fin_cases i
    · change dist (Real.pi / 2) a ≤ _
      rw [Real.dist_eq, abs_sub_comm]
      exact le_max_of_le_left (le_max_left _ _)
    · change dist (Real.pi / 2) b ≤ _
      rw [Real.dist_eq, abs_sub_comm]
      exact le_max_of_le_left (le_max_right _ _)
    · change dist (Real.pi / 2) c ≤ _
      rw [Real.dist_eq, abs_sub_comm]
      exact le_max_right _ _
  · have h0 := dist_le_pi_dist threeCenter ![a, b, c] 0
    have h1 := dist_le_pi_dist threeCenter ![a, b, c] 1
    have h2 := dist_le_pi_dist threeCenter ![a, b, c] 2
    change dist (Real.pi / 2) a ≤ _ at h0
    change dist (Real.pi / 2) b ≤ _ at h1
    change dist (Real.pi / 2) c ≤ _ at h2
    rw [Real.dist_eq, abs_sub_comm] at h0 h1 h2
    exact max_le (max_le h0 h1) h2

/-- Core identity: for `ψ ∈ [0, π/3]` and `(a, b, c) = (ψ, 2π/3 - ψ, 2π/3 + ψ)`,
`max |· - π/2| = π/3 + |min - π/6|`. -/
theorem three_anchor_sup_core {ψ a b c : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ Real.pi / 3)
    (ha : a = ψ) (hb : b = 2 * Real.pi / 3 - ψ) (hc : c = 2 * Real.pi / 3 + ψ) :
    max (max |a - Real.pi / 2| |b - Real.pi / 2|) |c - Real.pi / 2| =
      Real.pi / 3 + |min (min a b) c - Real.pi / 6| := by
  have hπ := Real.pi_pos
  rw [ha, hb, hc, abs_of_nonpos (by linarith : ψ - Real.pi / 2 ≤ 0),
    abs_of_nonneg (by linarith : 0 ≤ 2 * Real.pi / 3 + ψ - Real.pi / 2),
    min_eq_left (by linarith : ψ ≤ 2 * Real.pi / 3 - ψ),
    min_eq_left (by linarith : ψ ≤ 2 * Real.pi / 3 + ψ)]
  rcases le_total ψ (Real.pi / 6) with h | h
  · rw [abs_of_nonneg (by linarith : 0 ≤ 2 * Real.pi / 3 - ψ - Real.pi / 2),
      abs_of_nonpos (by linarith : ψ - Real.pi / 6 ≤ 0)]
    simp only [max_def]
    split_ifs <;> linarith
  · rw [abs_of_nonpos (by linarith : 2 * Real.pi / 3 - ψ - Real.pi / 2 ≤ 0),
      abs_of_nonneg (by linarith : 0 ≤ ψ - Real.pi / 6)]
    simp only [max_def]
    split_ifs <;> linarith

/-- **Exact sup-distance from the centre.** With `ψ` the distance from `θ` to the nearest
anchor, `dist (π/2, π/2, π/2) (threePointMap F (F.ι θ)) = π / 3 + |ψ - π / 6|`. In every
sector the three anchor distances are a permutation of `(ψ, 2π/3 - ψ, 2π/3 + ψ)`. -/
theorem threePointMap_boundary_dist_center (F : IsometricFilling M) (θ : Circle2Pi) :
    dist threeCenter (threePointMap F (F.ι θ)) =
      Real.pi / 3 + |min (min (dist θ 0) (dist θ ((2 * Real.pi / 3 : ℝ) : Circle2Pi)))
        (dist θ ((4 * Real.pi / 3 : ℝ) : Circle2Pi)) - Real.pi / 6| := by
  have hπ := Real.pi_pos
  rw [threePointMap_boundary_apply, dist_threeCenter]
  obtain ⟨t, ⟨ht₁, ht₂⟩, rfl⟩ := circle2Pi_exists_rep_Ioc θ
  rw [dist_coe_zero_of_abs_le (abs_le.2 ⟨by linarith, ht₂⟩)]
  rcases le_or_gt t (-(2 * Real.pi / 3)) with c₁ | c₁
  · rw [dist_coe_twoThirds_of_le ht₁ (by linarith), dist_coe_fourThirds_of_le ht₁ c₁,
      abs_of_neg (by linarith : t < 0)]
    have key := three_anchor_sup_core (ψ := -t - 2 * Real.pi / 3)
      (a := -t - 2 * Real.pi / 3) (b := t + 4 * Real.pi / 3) (c := -t)
      (by linarith) (by linarith) rfl (by ring) (by ring)
    simpa only [max_comm, max_left_comm, max_assoc, min_comm, min_left_comm, min_assoc]
      using key
  rcases le_or_gt t (-(Real.pi / 3)) with c₂ | c₂
  · rw [dist_coe_twoThirds_of_le ht₁ c₂, dist_coe_fourThirds_of_mem c₁.le (by linarith),
      abs_of_neg (by linarith : t < 0)]
    have key := three_anchor_sup_core (ψ := t + 2 * Real.pi / 3)
      (a := t + 2 * Real.pi / 3) (b := -t) (c := t + 4 * Real.pi / 3)
      (by linarith) (by linarith) rfl (by ring) (by ring)
    simpa only [max_comm, max_left_comm, max_assoc, min_comm, min_left_comm, min_assoc]
      using key
  rcases le_or_gt t 0 with c₃ | c₃
  · rw [dist_coe_twoThirds_of_mem c₂.le (by linarith),
      dist_coe_fourThirds_of_mem (by linarith) (by linarith), abs_of_nonpos c₃]
    have key := three_anchor_sup_core (ψ := -t)
      (a := -t) (b := t + 2 * Real.pi / 3) (c := 2 * Real.pi / 3 - t)
      (by linarith) (by linarith) rfl (by ring) (by ring)
    simpa only [max_comm, max_left_comm, max_assoc, min_comm, min_left_comm, min_assoc]
      using key
  rcases le_or_gt t (Real.pi / 3) with c₄ | c₄
  · rw [dist_coe_twoThirds_of_mem (by linarith) (by linarith),
      dist_coe_fourThirds_of_mem (by linarith) c₄, abs_of_pos c₃]
    have key := three_anchor_sup_core (ψ := t)
      (a := t) (b := 2 * Real.pi / 3 - t) (c := t + 2 * Real.pi / 3)
      (by linarith) (by linarith) rfl (by ring) (by ring)
    simpa only [max_comm, max_left_comm, max_assoc, min_comm, min_left_comm, min_assoc]
      using key
  rcases le_or_gt t (2 * Real.pi / 3) with c₅ | c₅
  · rw [dist_coe_twoThirds_of_mem (by linarith) c₅,
      dist_coe_fourThirds_of_ge c₄.le ht₂, abs_of_pos c₃]
    have key := three_anchor_sup_core (ψ := 2 * Real.pi / 3 - t)
      (a := 2 * Real.pi / 3 - t) (b := t) (c := 4 * Real.pi / 3 - t)
      (by linarith) (by linarith) rfl (by ring) (by ring)
    simpa only [max_comm, max_left_comm, max_assoc, min_comm, min_left_comm, min_assoc]
      using key
  · rw [dist_coe_twoThirds_of_ge c₅.le ht₂, dist_coe_fourThirds_of_ge (by linarith) ht₂,
      abs_of_pos c₃]
    have key := three_anchor_sup_core (ψ := t - 2 * Real.pi / 3)
      (a := t - 2 * Real.pi / 3) (b := 4 * Real.pi / 3 - t) (c := t)
      (by linarith) (by linarith) rfl (by ring) (by ring)
    simpa only [max_comm, max_left_comm, max_assoc, min_comm, min_left_comm, min_assoc]
      using key

/-- Every boundary image point is at sup-distance at least `π / 3` from the centre. -/
theorem pi_div_three_le_threePointMap_boundary_dist_center (F : IsometricFilling M)
    (θ : Circle2Pi) : Real.pi / 3 ≤ dist threeCenter (threePointMap F (F.ι θ)) := by
  rw [threePointMap_boundary_dist_center]
  linarith [abs_nonneg (min (min (dist θ 0) (dist θ ((2 * Real.pi / 3 : ℝ) : Circle2Pi)))
    (dist θ ((4 * Real.pi / 3 : ℝ) : Circle2Pi)) - Real.pi / 6)]

end

end

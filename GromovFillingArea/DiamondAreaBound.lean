/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.DiamondGeometry

/-!
# Universal `π² / 2` Filling Area Bound via Quarter-Circle Diamond Covering

This file constructs the radial `L¹`-to-`L²` gauge homeomorphism sending
`quarterDiamond` onto `Metric.closedBall (0 : ℂ) (Real.pi / 2)` and
`quarterDiamondBoundary` onto `Metric.sphere (0 : ℂ) (Real.pi / 2)`, applies
`disk_covered_of_no_retraction` to prove `quarterDiamond ⊆ range (quarterPairMap F)`,
and deduces the sharp quarter-circle universal lower bound
`ENNReal.ofReal (Real.pi ^ 2 / 2) ≤ hausdorffMeasure 2 (univ : Set M)` (`≈ 4.9348`).
-/

open MeasureTheory Metric Set BoundedContinuousFunction AddCircle Topology

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Radial `L¹`-to-`L²` gauge map centered at `(π / 2, π / 2)` sending `Fin 2 → ℝ` to `ℂ`
such that `‖diamondToComplex p‖ = |p 0 - Real.pi / 2| + |p 1 - Real.pi / 2|`. -/
def diamondToComplex (p : Fin 2 → ℝ) : ℂ :=
  let x := p 0 - Real.pi / 2
  let y := p 1 - Real.pi / 2
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  if z = 0 then 0 else (((|x| + |y|) / ‖z‖ : ℝ) : ℂ) * z

/-- The centred vector `(p 0 - π/2) + (p 1 - π/2) i` of `p`. -/
def diamondVec (p : Fin 2 → ℝ) : ℂ :=
  ((p 0 - Real.pi / 2 : ℝ) : ℂ) + ((p 1 - Real.pi / 2 : ℝ) : ℂ) * Complex.I

/-- The centred `L¹` gauge `|p 0 - π/2| + |p 1 - π/2|`. -/
def diamondGauge (p : Fin 2 → ℝ) : ℝ :=
  |p 0 - Real.pi / 2| + |p 1 - Real.pi / 2|

/-- Inverse gauge map `w ↦ (π/2, π/2) + (‖w‖ / (|re w| + |im w|)) (re w, im w)`
(at `w = 0` the factor is `0 / 0 = 0`). -/
def diamondFromComplex (w : ℂ) : Fin 2 → ℝ :=
  ![Real.pi / 2 + ‖w‖ / (|w.re| + |w.im|) * w.re,
    Real.pi / 2 + ‖w‖ / (|w.re| + |w.im|) * w.im]

theorem diamondVec_re (p : Fin 2 → ℝ) : (diamondVec p).re = p 0 - Real.pi / 2 := by
  simp [diamondVec]

theorem diamondVec_im (p : Fin 2 → ℝ) : (diamondVec p).im = p 1 - Real.pi / 2 := by
  simp [diamondVec]

theorem diamondGauge_nonneg (p : Fin 2 → ℝ) : 0 ≤ diamondGauge p := by
  unfold diamondGauge
  positivity

theorem diamondToComplex_eq (p : Fin 2 → ℝ) :
    diamondToComplex p = if diamondVec p = 0 then 0 else
      ((diamondGauge p / ‖diamondVec p‖ : ℝ) : ℂ) * diamondVec p := rfl

theorem diamondVec_eq_zero_iff (p : Fin 2 → ℝ) : diamondVec p = 0 ↔ diamondGauge p = 0 := by
  constructor
  · intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    rw [diamondVec_re, Complex.zero_re] at h1
    rw [diamondVec_im, Complex.zero_im] at h2
    rw [diamondGauge, h1, h2, abs_zero, add_zero]
  · intro h
    have h1 : |p 0 - Real.pi / 2| = 0 := le_antisymm
      (by unfold diamondGauge at h; linarith [abs_nonneg (p 1 - Real.pi / 2)]) (abs_nonneg _)
    have h2 : |p 1 - Real.pi / 2| = 0 := le_antisymm
      (by unfold diamondGauge at h; linarith [abs_nonneg (p 0 - Real.pi / 2)]) (abs_nonneg _)
    apply Complex.ext
    · rw [diamondVec_re, Complex.zero_re]
      exact abs_eq_zero.mp h1
    · rw [diamondVec_im, Complex.zero_im]
      exact abs_eq_zero.mp h2

/-- `‖diamondToComplex p‖ = |p 0 - π/2| + |p 1 - π/2|`. -/
theorem norm_diamondToComplex (p : Fin 2 → ℝ) : ‖diamondToComplex p‖ = diamondGauge p := by
  rw [diamondToComplex_eq]
  split_ifs with hz
  · rw [norm_zero]
    exact ((diamondVec_eq_zero_iff p).mp hz).symm
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (diamondGauge_nonneg p) (norm_nonneg _)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz)]

/-- `diamondFromComplex` is a left inverse of `diamondToComplex`. -/
theorem diamondFromComplex_diamondToComplex (p : Fin 2 → ℝ) :
    diamondFromComplex (diamondToComplex p) = p := by
  by_cases hz : diamondVec p = 0
  · have h0 : diamondToComplex p = 0 := by rw [diamondToComplex_eq, if_pos hz]
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    rw [diamondVec_re, Complex.zero_re] at hre
    rw [diamondVec_im, Complex.zero_im] at him
    rw [h0, diamondFromComplex]
    funext i
    fin_cases i <;> simp <;> linarith
  · have hn : 0 < diamondGauge p := lt_of_le_of_ne (diamondGauge_nonneg p)
      (fun h => hz ((diamondVec_eq_zero_iff p).mpr h.symm))
    have hz' : 0 < ‖diamondVec p‖ := norm_pos_iff.mpr hz
    obtain ⟨r, hr⟩ : ∃ r, r = diamondGauge p / ‖diamondVec p‖ := ⟨_, rfl⟩
    have hr0 : 0 < r := by
      rw [hr]
      positivity
    have hG : diamondToComplex p = (r : ℂ) * diamondVec p := by
      rw [diamondToComplex_eq, if_neg hz, hr]
    have hre : (diamondToComplex p).re = r * (p 0 - Real.pi / 2) := by
      rw [hG, Complex.re_ofReal_mul, diamondVec_re]
    have him : (diamondToComplex p).im = r * (p 1 - Real.pi / 2) := by
      rw [hG, Complex.im_ofReal_mul, diamondVec_im]
    have hsum : |(diamondToComplex p).re| + |(diamondToComplex p).im| =
        r * diamondGauge p := by
      rw [hre, him, abs_mul, abs_mul, abs_of_pos hr0, diamondGauge]
      ring
    have hcoef : ‖diamondToComplex p‖ /
        (|(diamondToComplex p).re| + |(diamondToComplex p).im|) = r⁻¹ := by
      rw [norm_diamondToComplex, hsum]
      field_simp
    rw [diamondFromComplex, hcoef, hre, him]
    funext i
    fin_cases i <;> simp [hr0.ne']

theorem diamondToComplex_injective : Function.Injective diamondToComplex :=
  Function.LeftInverse.injective diamondFromComplex_diamondToComplex

theorem diamondVec_diamondFromComplex (w : ℂ) :
    diamondVec (diamondFromComplex w) = ((‖w‖ / (|w.re| + |w.im|) : ℝ) : ℂ) * w := by
  apply Complex.ext
  · rw [diamondVec_re, Complex.re_ofReal_mul, diamondFromComplex]
    simp
  · rw [diamondVec_im, Complex.im_ofReal_mul, diamondFromComplex]
    simp

theorem abs_re_add_abs_im_pos {w : ℂ} (hw : w ≠ 0) : 0 < |w.re| + |w.im| := by
  by_contra h
  push_neg at h
  have h1 : w.re = 0 := abs_eq_zero.mp
    (le_antisymm (by linarith [abs_nonneg w.im]) (abs_nonneg _))
  have h2 : w.im = 0 := abs_eq_zero.mp
    (le_antisymm (by linarith [abs_nonneg w.re]) (abs_nonneg _))
  exact hw (Complex.ext h1 h2)

theorem diamondGauge_diamondFromComplex {w : ℂ} (hw : w ≠ 0) :
    diamondGauge (diamondFromComplex w) = ‖w‖ := by
  have hm := abs_re_add_abs_im_pos hw
  have hs0 : 0 ≤ ‖w‖ / (|w.re| + |w.im|) := by positivity
  rw [diamondGauge, ← diamondVec_re, ← diamondVec_im, diamondVec_diamondFromComplex,
    Complex.re_ofReal_mul, Complex.im_ofReal_mul, abs_mul, abs_mul, abs_of_nonneg hs0,
    ← mul_add]
  field_simp

/-- `diamondFromComplex` is a right inverse of `diamondToComplex` away from `0`. -/
theorem diamondToComplex_diamondFromComplex {w : ℂ} (hw : w ≠ 0) :
    diamondToComplex (diamondFromComplex w) = w := by
  have hm := abs_re_add_abs_im_pos hw
  have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  obtain ⟨s, hs⟩ : ∃ s, s = ‖w‖ / (|w.re| + |w.im|) := ⟨_, rfl⟩
  have hs0 : 0 < s := by
    rw [hs]
    have := norm_pos_iff.mpr hw
    positivity
  have hvec : diamondVec (diamondFromComplex w) = (s : ℂ) * w := by
    rw [diamondVec_diamondFromComplex, hs]
  have hne : diamondVec (diamondFromComplex w) ≠ 0 := by
    rw [hvec]
    exact mul_ne_zero (by exact_mod_cast hs0.ne') hw
  rw [diamondToComplex_eq, if_neg hne, diamondGauge_diamondFromComplex hw, hvec, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0, ← mul_assoc, ← Complex.ofReal_mul,
    show ‖w‖ / (s * ‖w‖) * s = 1 by field_simp, Complex.ofReal_one, one_mul]

/-- `diamondToComplex` is continuous: off the centre it is a product of continuous maps, and
at the centre `‖diamondToComplex q‖ = diamondGauge q → 0`. -/
theorem continuous_diamondToComplex : Continuous diamondToComplex := by
  have hvec : Continuous diamondVec := by
    unfold diamondVec
    fun_prop
  have hgauge : Continuous diamondGauge := by
    unfold diamondGauge
    fun_prop
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hz : diamondVec p = 0
  · have h0 : diamondToComplex p = 0 := by rw [diamondToComplex_eq, if_pos hz]
    rw [ContinuousAt, h0, tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_diamondToComplex]
    have := hgauge.tendsto p
    rwa [(diamondVec_eq_zero_iff p).mp hz] at this
  · have hU : {q | diamondVec q ≠ 0} ∈ 𝓝 p :=
      (isOpen_ne_fun hvec continuous_const).mem_nhds hz
    have hform : ContinuousAt
        (fun q => ((diamondGauge q / ‖diamondVec q‖ : ℝ) : ℂ) * diamondVec q) p :=
      (Complex.continuous_ofReal.continuousAt.comp
        (hgauge.continuousAt.div hvec.norm.continuousAt (norm_ne_zero_iff.mpr hz))).mul
        hvec.continuousAt
    refine hform.congr (Filter.eventuallyEq_of_mem hU fun q hq => ?_)
    rw [diamondToComplex_eq, if_neg hq]

/-- The quarter pair map on the boundary is `θ ↦ ![d(θ, 0), d(θ, π/2)]`. -/
theorem quarterPairMap_boundary_apply (F : IsometricFilling M) (θ : Circle2Pi) :
    quarterPairMap F (F.ι θ) = ![dist θ 0, dist θ ((Real.pi / 2 : ℝ) : Circle2Pi)] := by
  rw [quarterPairMap, kuratowskiMap_boundary, kuratowskiMap_boundary]

theorem diamondToComplex_boundary_mem_sphere (F : IsometricFilling M) (θ : Circle2Pi) :
    diamondToComplex (quarterPairMap F (F.ι θ)) ∈ sphere (0 : ℂ) (Real.pi / 2) := by
  rw [mem_sphere_zero_iff_norm, norm_diamondToComplex, diamondGauge,
    quarterPairMap_boundary_apply]
  have := quarterCircle_boundary_diamond θ
  rw [dist_comm (0 : Circle2Pi) θ, dist_comm ((Real.pi / 2 : ℝ) : Circle2Pi) θ] at this
  exact this

/-- Every point `(π/2 + x, π/2 + y)` of the diamond boundary is `(d(θ, 0), d(θ, π/2))` for
some boundary angle `θ`, chosen explicitly in each quadrant of `(x, y)`. -/
theorem exists_boundary_angle {x y : ℝ} (h : |x| + |y| = Real.pi / 2) :
    ∃ θ : Circle2Pi, dist θ 0 = Real.pi / 2 + x ∧
      dist θ ((Real.pi / 2 : ℝ) : Circle2Pi) = Real.pi / 2 + y := by
  have hπ := Real.pi_pos
  have hu : ∀ t : ℝ, |t| ≤ Real.pi → dist (t : Circle2Pi) 0 = |t| := fun t ht => by
    rw [dist_zero_right, circle2Pi_norm_coe_of_abs_le t ht]
  rcases le_or_gt y 0 with hy0 | hy0 <;> rcases le_or_gt x 0 with hx0 | hx0
  · -- `x ≤ 0, y ≤ 0`: `t = -y ∈ [0, π/2]`
    rw [abs_of_nonpos hx0, abs_of_nonpos hy0] at h
    refine ⟨((-y : ℝ) : Circle2Pi), ?_, ?_⟩
    · rw [hu _ (by rw [abs_of_nonneg (by linarith)]; linarith), abs_of_nonneg (by linarith)]
      linarith
    · rw [dist_coe_halfPi_of_abs_le (by linarith) (by linarith)]
      ring
  · -- `x > 0, y ≤ 0`: `t = x + π/2 ∈ (π/2, π]`
    rw [abs_of_pos hx0, abs_of_nonpos hy0] at h
    refine ⟨((x + Real.pi / 2 : ℝ) : Circle2Pi), ?_, ?_⟩
    · rw [hu _ (by rw [abs_of_nonneg (by linarith)]; linarith), abs_of_nonneg (by linarith)]
      ring
    · rw [dist_coe_halfPi_of_ge (by linarith) (by linarith)]
      linarith
  · -- `x ≤ 0, y > 0`: `t = -y ∈ [-π/2, 0)`
    rw [abs_of_nonpos hx0, abs_of_pos hy0] at h
    refine ⟨((-y : ℝ) : Circle2Pi), ?_, ?_⟩
    · rw [hu _ (by rw [abs_of_nonpos (by linarith)]; linarith), abs_of_nonpos (by linarith)]
      linarith
    · rw [dist_coe_halfPi_of_abs_le (by linarith) (by linarith)]
      ring
  · -- `x > 0, y > 0`: `t = -x - π/2 ∈ (-π, -π/2)`
    rw [abs_of_pos hx0, abs_of_pos hy0] at h
    refine ⟨((-x - Real.pi / 2 : ℝ) : Circle2Pi), ?_, ?_⟩
    · rw [hu _ (by rw [abs_of_neg (by linarith)]; linarith), abs_of_neg (by linarith)]
      ring
    · rw [dist_coe_halfPi_of_le_neg (by linarith) (by linarith)]
      linarith

/-- The boundary map `θ ↦ diamondToComplex (quarterPairMap F (F.ι θ))` hits every point of
`sphere 0 (π/2)`. -/
theorem diamondToComplex_boundary_surjective (F : IsometricFilling M) {w : ℂ}
    (hw : w ∈ sphere (0 : ℂ) (Real.pi / 2)) :
    ∃ θ : Circle2Pi, diamondToComplex (quarterPairMap F (F.ι θ)) = w := by
  have hπ := Real.pi_pos
  rw [mem_sphere_zero_iff_norm] at hw
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    linarith
  obtain ⟨p, hp⟩ : ∃ p, p = diamondFromComplex w := ⟨_, rfl⟩
  have hgauge : |p 0 - Real.pi / 2| + |p 1 - Real.pi / 2| = Real.pi / 2 := by
    change diamondGauge p = Real.pi / 2
    rw [hp, diamondGauge_diamondFromComplex hw0, hw]
  obtain ⟨θ, h0, h1⟩ := exists_boundary_angle hgauge
  refine ⟨θ, ?_⟩
  have hq : quarterPairMap F (F.ι θ) = p := by
    rw [quarterPairMap_boundary_apply]
    funext i
    fin_cases i
    · change dist θ 0 = p 0
      rw [h0]
      ring
    · change dist θ ((Real.pi / 2 : ℝ) : Circle2Pi) = p 1
      rw [h1]
      ring
  rw [hq, hp, diamondToComplex_diamondFromComplex hw0]

/-- **Lemma 1 (Quarter-Diamond Covering by `quarterPairMap F`):**
Every point of `quarterDiamond` lies in `range (quarterPairMap F)`. -/
theorem quarterDiamond_subset_range (F : IsometricFilling M) :
    quarterDiamond ⊆ range (quarterPairMap F) := by
  have hπ := Real.pi_pos
  have hf : Continuous (diamondToComplex ∘ quarterPairMap F) :=
    continuous_diamondToComplex.comp (quarterPairMap_lipschitzWith F).continuous
  let g : Circle2Pi → sphere (0 : ℂ) (Real.pi / 2) := fun θ =>
    ⟨diamondToComplex (quarterPairMap F (F.ι θ)), diamondToComplex_boundary_mem_sphere F θ⟩
  have hg_cont : Continuous g :=
    (hf.comp F.isometry_ι.continuous).subtype_mk _
  have hg_bij : Function.Bijective g := by
    refine ⟨fun θ₁ θ₂ h => quarterPairMap_boundary_injective F
      (diamondToComplex_injective (congrArg Subtype.val h)), ?_⟩
    rintro ⟨w, hw⟩
    obtain ⟨θ, hθ⟩ := diamondToComplex_boundary_surjective F hw
    exact ⟨θ, Subtype.ext hθ⟩
  let e : Circle2Pi ≃ₜ sphere (0 : ℂ) (Real.pi / 2) :=
    hg_cont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hg_bij)
  have hcov := disk_covered_of_no_retraction F (by positivity : (0 : ℝ) < Real.pi / 2)
    (diamondToComplex ∘ quarterPairMap F) hf e (fun _ => rfl) F.no_boundary_retraction
  intro p hp
  have hmem : diamondToComplex p ∈ closedBall (0 : ℂ) (Real.pi / 2) := by
    rw [mem_closedBall_zero_iff, norm_diamondToComplex]
    exact hp
  obtain ⟨x, hx⟩ := hcov hmem
  exact ⟨x, diamondToComplex_injective hx⟩

/-- **Main Upgraded Theorem (Universal `π² / 2` Filling Area Lower Bound):**
Every topological isometric filling `F : IsometricFilling M` has `2`-dimensional
Hausdorff area at least `ENNReal.ofReal (Real.pi ^ 2 / 2)` (`≈ 4.9348`), lifting
`gromov_universal_pi_bound` (`π ≈ 3.14159`) by a factor of `π / 2`. -/
theorem gromov_universal_pi_sq_div_two_bound (F : IsometricFilling M) :
    ENNReal.ofReal (Real.pi ^ 2 / 2) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) := by
  have himg := (quarterPairMap_lipschitzWith F).hausdorffMeasure_image_le (d := 2)
    (by norm_num) (univ : Set M)
  rw [image_univ, ENNReal.coe_one, ENNReal.one_rpow, one_mul] at himg
  rw [← hausdorffMeasure_two_quarterDiamond]
  exact (measure_mono (quarterDiamond_subset_range F)).trans himg

end

end

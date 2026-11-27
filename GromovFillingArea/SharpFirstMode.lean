/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.UniversalAreaBound

/-!
# Sharp `(2 / π)`-Lipschitz Constant & `π` Filling Area Lower Bound

This file formalizes the improvement discovered by `scripts/conjecture_discovery.py`:
because the average of `|cos(θ - φ)|` over `[0, 2π]` is `2 / π`, the fundamental
Fourier projection `fourierProj 1 : (Circle2Pi →ᵇ ℝ) → ℂ` has sharp Lipschitz
constant `2 / π` rather than `1`. Combining this with `2`-dimensional Hausdorff
scaling (`(2 / π) ^ 2 = 4 / π ^ 2`) lifts `gromov_universal_four_div_pi_bound`
from `4 / π` to `ENNReal.ofReal Real.pi ≤ hausdorffMeasure 2 (univ : Set M)`.
-/

open MeasureTheory Metric Set BoundedContinuousFunction AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- `∫₀^{2π} |cos (x + φ)| dx = 4` for every phase `φ`: shift to `[-π/2, 3π/2]` by
periodicity and split at the zero `π / 2` of `cos`. -/
theorem integral_abs_cos_add (φ : ℝ) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), |Real.cos (x + φ)| = 4 := by
  have hπ := Real.pi_pos
  have hper : Function.Periodic (fun x => |Real.cos x|) (2 * Real.pi) := fun x => by
    dsimp only
    rw [Real.cos_periodic x]
  have hshift := intervalIntegral.integral_comp_add_right (a := 0) (b := 2 * Real.pi)
    (fun x => |Real.cos x|) φ
  rw [hshift, zero_add, add_comm (2 * Real.pi) φ,
    hper.intervalIntegral_add_eq φ (-(Real.pi / 2))]
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun x => |Real.cos x|) volume a b :=
    fun a b => Real.continuous_cos.abs.intervalIntegrable a b
  have h1 : ∫ x in (-(Real.pi / 2))..(Real.pi / 2), |Real.cos x| = 2 := by
    rw [intervalIntegral.integral_congr (g := Real.cos) (fun x hx => ?_), integral_cos,
      Real.sin_pi_div_two, Real.sin_neg, Real.sin_pi_div_two]
    · norm_num
    · rw [Set.uIcc_of_le (by linarith)] at hx
      exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc hx)
  have h2 : ∫ x in (Real.pi / 2)..(-(Real.pi / 2) + 2 * Real.pi), |Real.cos x| = 2 := by
    rw [intervalIntegral.integral_congr (g := fun x => -Real.cos x) (fun x hx => ?_),
      intervalIntegral.integral_neg, integral_cos]
    · rw [show -(Real.pi / 2) + 2 * Real.pi = Real.pi / 2 + Real.pi by ring,
        Real.sin_add_pi, Real.sin_pi_div_two]
      ring
    · rw [Set.uIcc_of_le (by linarith)] at hx
      exact abs_of_nonpos (Real.cos_nonpos_of_pi_div_two_le_of_le hx.1 (by linarith [hx.2]))
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint _ (Real.pi / 2)) (hint _ _),
    h1, h2]
  norm_num

/-- The coercion `ℝ → Circle2Pi` is continuous. -/
theorem continuous_coe_circle2Pi : Continuous (fun x : ℝ => (x : Circle2Pi)) :=
  continuous_quotient_mk'

/-- Rotating the first Fourier coefficient by `exp (φ i)` and taking the real part gives
the real integral `(2π)⁻¹ ∫₀^{2π} cos (x - φ) δ(x) dx`. -/
theorem re_exp_mul_fourierProj_one (δ : Circle2Pi →ᵇ ℝ) (φ : ℝ) :
    (Complex.exp (φ * Complex.I) * fourierProj 1 δ).re =
      (2 * Real.pi)⁻¹ * ∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos (x + -φ) * δ x := by
  have hδ : Continuous (fun x : ℝ => δ x) := δ.continuous.comp continuous_coe_circle2Pi
  rw [fourierProj, fourierCoeff_eq_intervalIntegral _ _ 0, zero_add]
  simp_rw [fourier_neg_coe_eq_cexp, smul_eq_mul]
  rw [Complex.real_smul, mul_left_comm, ← intervalIntegral.integral_const_mul,
    Complex.re_ofReal_mul, one_div]
  congr 1
  have hcont : Continuous (fun x : ℝ => Complex.exp (φ * Complex.I) *
      (Complex.exp (-((1 : ℤ) : ℂ) * Complex.I * x) * (δ x : ℂ))) := by
    have := Complex.continuous_ofReal.comp hδ
    fun_prop
  rw [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm
    (hcont.intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [Complex.reCLM_apply]
  rw [← mul_assoc, ← Complex.exp_add,
    show φ * Complex.I + -((1 : ℤ) : ℂ) * Complex.I * x = ((φ - x : ℝ) : ℂ) * Complex.I by
      push_cast; ring,
    Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re,
    show x + -φ = -(φ - x) by ring, Real.cos_neg]

/-- `Re (exp (φ i) · f̂_δ(1)) ≤ (2 / π) ‖δ‖`, from `|cos| ≤ 1` pointwise only through
`∫₀^{2π} |cos (x - φ)| = 4`. -/
theorem re_exp_mul_fourierProj_one_le (δ : Circle2Pi →ᵇ ℝ) (φ : ℝ) :
    (Complex.exp (φ * Complex.I) * fourierProj 1 δ).re ≤ 2 / Real.pi * ‖δ‖ := by
  have hπ := Real.pi_pos
  have hδ : Continuous (fun x : ℝ => δ x) := δ.continuous.comp continuous_coe_circle2Pi
  have hc : Continuous (fun x : ℝ => Real.cos (x + -φ)) := by fun_prop
  rw [re_exp_mul_fourierProj_one]
  have hb : (∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos (x + -φ) * δ x) ≤
      ∫ x in (0 : ℝ)..(2 * Real.pi), ‖δ‖ * |Real.cos (x + -φ)| := by
    refine intervalIntegral.integral_mono_on (by positivity)
      ((hc.mul hδ).intervalIntegrable _ _)
      ((continuous_const.mul hc.abs).intervalIntegrable _ _) (fun x _ => ?_)
    have hx : |δ x| ≤ ‖δ‖ := by
      rw [← Real.norm_eq_abs]
      exact δ.norm_coe_le_norm x
    calc Real.cos (x + -φ) * δ x ≤ |Real.cos (x + -φ) * δ x| := le_abs_self _
      _ = |Real.cos (x + -φ)| * |δ x| := abs_mul _ _
      _ ≤ |Real.cos (x + -φ)| * ‖δ‖ := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
      _ = ‖δ‖ * |Real.cos (x + -φ)| := mul_comm _ _
  rw [intervalIntegral.integral_const_mul, integral_abs_cos_add] at hb
  calc (2 * Real.pi)⁻¹ * ∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos (x + -φ) * δ x
      ≤ (2 * Real.pi)⁻¹ * (‖δ‖ * 4) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 2 / Real.pi * ‖δ‖ := by
      field_simp
      ring

/-- **Lemma 1 (Sharp `(2 / π)` Lipschitz Constant of `fourierProj 1`):**
For any `g h : Circle2Pi →ᵇ ℝ`,
`‖fourierProj 1 g - fourierProj 1 h‖ ≤ (2 / Real.pi) * dist g h`. -/
theorem fourierProj_one_sharp_lipschitz :
    LipschitzWith ⟨2 / Real.pi, by positivity⟩ (fourierProj 1) := by
  refine LipschitzWith.of_dist_le_mul fun g h => ?_
  change dist (fourierProj 1 g) (fourierProj 1 h) ≤ 2 / Real.pi * dist g h
  rw [dist_eq_norm, dist_eq_norm, fourierProj, fourierProj,
    ← fourierCoeff_sub_of_continuous _ _ (bcf_complex_continuous g) (bcf_complex_continuous h)]
  have hfun : (fun θ : Circle2Pi => (g θ : ℂ) - (h θ : ℂ)) =
      fun θ : Circle2Pi => (((g - h) θ : ℝ) : ℂ) := by
    funext θ
    simp
  rw [hfun]
  set w := fourierCoeff (fun θ : Circle2Pi => (((g - h) θ : ℝ) : ℂ)) 1 with hw_def
  -- unit-direction projection: `‖w‖ = Re (exp (-arg w · i) · w)`
  have hw : ‖w‖ = (Complex.exp (((-Complex.arg w : ℝ) : ℂ) * Complex.I) * w).re := by
    calc ‖w‖ = ((‖w‖ : ℂ)).re := (Complex.ofReal_re _).symm
      _ = (Complex.exp (((-Complex.arg w : ℝ) : ℂ) * Complex.I) *
            (‖w‖ * Complex.exp (Complex.arg w * Complex.I))).re := by
          rw [mul_left_comm, ← Complex.exp_add]
          push_cast
          rw [neg_mul, neg_add_cancel, Complex.exp_zero, mul_one]
      _ = _ := by rw [Complex.norm_mul_exp_arg_mul_I w]
  rw [hw]
  exact re_exp_mul_fourierProj_one_le (g - h) _

/-- **Main Upgraded Theorem (Universal `π` Filling Area Lower Bound):**
Every topological isometric filling `F : IsometricFilling M` has `2`-dimensional
Hausdorff area at least `ENNReal.ofReal Real.pi` (`≈ 3.14159`), strengthening
`gromov_universal_four_div_pi_bound` (`4 / π ≈ 1.273`) by a factor of `π² / 4`. -/
theorem gromov_universal_pi_bound (F : IsometricFilling M) :
    ENNReal.ofReal Real.pi ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) := by
  have hπ := Real.pi_pos
  set f : M → ℂ := fourierProj 1 ∘ kuratowskiBanach F with hf_def
  set K : NNReal := ⟨2 / Real.pi, by positivity⟩ with hK_def
  have hKr : (K : ℝ) = 2 / Real.pi := rfl
  have hlip : LipschitzWith K f :=
    (fourierProj_one_sharp_lipschitz.comp (kuratowskiBanach_lipschitzWith F)).weaken
      (le_of_eq (mul_one _))
  have hcover := disk_covered_of_no_retraction F (by positivity : (0 : ℝ) < 2 / Real.pi) f
    hlip.continuous (fourierProjOneBoundaryHomeomorph F) (fun _ => rfl)
    F.no_boundary_retraction
  have himg := hlip.hausdorffMeasure_image_le (d := 2) (by norm_num) (univ : Set M)
  rw [image_univ] at himg
  have hK : (K : ENNReal) ^ (2 : ℝ) = ENNReal.ofReal (4 / Real.pi ^ 2) := by
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_coe_nnreal, hKr,
      ← ENNReal.ofReal_pow (by positivity)]
    congr 1
    ring
  -- `4 / π ≤ μH (closedBall 0 (2/π)) ≤ μH (range f) ≤ (2/π)² μH univ`
  have h4 : ENNReal.ofReal (4 / Real.pi) ≤
      ENNReal.ofReal (4 / Real.pi ^ 2) *
        MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) := by
    rw [← hK]
    exact hausdorffMeasure_two_fundamental_disk.trans ((measure_mono hcover).trans himg)
  calc ENNReal.ofReal Real.pi
      = ENNReal.ofReal (Real.pi ^ 2 / 4) * ENNReal.ofReal (4 / Real.pi) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ ≤ ENNReal.ofReal (Real.pi ^ 2 / 4) * (ENNReal.ofReal (4 / Real.pi ^ 2) *
          MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M)) := by gcongr
    _ = MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          show Real.pi ^ 2 / 4 * (4 / Real.pi ^ 2) = 1 by field_simp, ENNReal.ofReal_one,
          one_mul]

end

end

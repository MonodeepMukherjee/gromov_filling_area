/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.BoundaryWinding

/-!
# Closed-Form Radial Retraction onto `Sphere (0 : ℂ) R`

This file constructs the explicit radial ray projection `radialProj p R : ℂ → ℂ`
from an interior point `p ∈ Metric.ball (0 : ℂ) R` (`‖p‖ < R`) onto the boundary
circle `Metric.sphere (0 : ℂ) R`, proving that `‖radialProj p R z‖ = R` for all
`z ≠ p` and `radialProj p R z = z` whenever `‖z‖ = R`.
-/

open MeasureTheory Metric Set Complex

@[expose] public section

noncomputable section

/-- The positive ray parameter `t > 0` where `p + t • (z - p)` intersects `sphere 0 R`,
given by the positive root of `‖z - p‖² t² + 2 Re(⟨p, z - p⟩) t + (‖p‖² - R²) = 0`. -/
def radialRayParam (p : ℂ) (R : ℝ) (z : ℂ) : ℝ :=
  let d := z - p
  let a := Complex.normSq d
  let b := (p * starRingEnd ℂ d).re
  let c := Complex.normSq p - R ^ 2
  (-b + Real.sqrt (b ^ 2 - a * c)) / a

/-- The radial projection from `p` through `z` onto `Metric.sphere (0 : ℂ) R`. -/
def radialProj (p : ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  p + (radialRayParam p R z : ℂ) * (z - p)

/-- Expansion of `normSq (p + t d)` as a real quadratic in `t`. -/
theorem normSq_add_ofReal_mul (p d : ℂ) (t : ℝ) :
    Complex.normSq (p + (t : ℂ) * d) =
      Complex.normSq p + 2 * t * (p * starRingEnd ℂ d).re + t ^ 2 * Complex.normSq d := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The positive root `t = (-b + √(b² - a c)) / a` solves `a t² + 2 b t + c = 0`. -/
theorem quadratic_pos_root {a b c t : ℝ} (ha : 0 < a) (hdisc : 0 ≤ b ^ 2 - a * c)
    (ht : t = (-b + Real.sqrt (b ^ 2 - a * c)) / a) :
    a * t ^ 2 + 2 * b * t + c = 0 := by
  have hat : a * t = -b + Real.sqrt (b ^ 2 - a * c) := by
    rw [ht]
    field_simp
  have hs := Real.sq_sqrt hdisc
  have h : a * (a * t ^ 2 + 2 * b * t + c) = 0 := by
    linear_combination (a * t + Real.sqrt (b ^ 2 - a * c) + b) * hat + hs
  exact (mul_eq_zero.mp h).resolve_left ha.ne'

/-- If `c + 2 b + a = 0`, `a > 0` and `c < 0`, the positive root equals `1`. -/
theorem quadratic_pos_root_eq_one {a b c : ℝ} (ha : 0 < a) (hrel : c + 2 * b + a = 0)
    (hc : c < 0) :
    (-b + Real.sqrt (b ^ 2 - a * c)) / a = 1 := by
  have hab : 0 < a + b := by linarith
  have hsq : b ^ 2 - a * c = (a + b) ^ 2 := by
    linear_combination (-a) * hrel
  rw [hsq, Real.sqrt_sq hab.le, div_eq_one_iff_eq ha.ne']
  ring

/-- **Lemma 1 (Image Lies on `Sphere (0 : ℂ) R`):**
For any `p` with `‖p‖ < R` and any `z ≠ p`, `radialProj p R z` lies on
`Metric.sphere (0 : ℂ) R`. -/
theorem radialProj_mem_sphere {p z : ℂ} {R : ℝ} (hR : 0 < R) (hp : ‖p‖ < R) (hz : z ≠ p) :
    radialProj p R z ∈ Metric.sphere (0 : ℂ) R := by
  have ha : 0 < Complex.normSq (z - p) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hz)
  have hc : Complex.normSq p - R ^ 2 < 0 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg p]
  have hdisc : 0 ≤ ((p * starRingEnd ℂ (z - p)).re) ^ 2 -
      Complex.normSq (z - p) * (Complex.normSq p - R ^ 2) := by
    nlinarith [sq_nonneg ((p * starRingEnd ℂ (z - p)).re), mul_pos ha (neg_pos.mpr hc)]
  have hq := quadratic_pos_root (t := radialRayParam p R z) ha hdisc rfl
  have hsq : ‖radialProj p R z‖ ^ 2 = R ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, radialProj, normSq_add_ofReal_mul]
    linarith
  rw [mem_sphere_zero_iff_norm]
  exact (pow_left_inj₀ (norm_nonneg _) hR.le two_ne_zero).mp hsq

/-- **Lemma 2 (Fixes `Sphere (0 : ℂ) R` Pointwise):**
If `‖p‖ < R` and `z ∈ Metric.sphere (0 : ℂ) R`, then `radialProj p R z = z`. -/
theorem radialProj_eq_self_of_mem_sphere {p z : ℂ} {R : ℝ}
    (hR : 0 < R) (hp : ‖p‖ < R) (hz : z ∈ Metric.sphere (0 : ℂ) R) :
    radialProj p R z = z := by
  have hzR := mem_sphere_zero_iff_norm.mp hz
  have hzp : z ≠ p := by
    rintro rfl
    linarith
  have ha : 0 < Complex.normSq (z - p) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hzp)
  have hc : Complex.normSq p - R ^ 2 < 0 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg p]
  have h1 := normSq_add_ofReal_mul p (z - p) 1
  rw [Complex.ofReal_one, one_mul, add_sub_cancel, Complex.normSq_eq_norm_sq z, hzR] at h1
  have hrel : (Complex.normSq p - R ^ 2) + 2 * (p * starRingEnd ℂ (z - p)).re +
      Complex.normSq (z - p) = 0 := by
    linarith
  have ht : radialRayParam p R z = 1 := quadratic_pos_root_eq_one ha hrel hc
  rw [radialProj, ht, Complex.ofReal_one, one_mul, add_sub_cancel]

end

end

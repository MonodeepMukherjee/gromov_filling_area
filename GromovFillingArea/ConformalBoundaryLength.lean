/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.WeightedRadialBound

/-!
# Boundary Circumference & Weighted Hemisphere Moment Bound

This file formalizes the boundary circumference condition `2 * π ≤ conformalBoundaryLength lam`
for conformal disks `λ(r, θ)² (dr² + r² dθ²)` and derives the sharp `2 * π` area bound from
the weighted hemisphere moment inequality
`∫₀¹ r · h(r)² dr ≤ ∫₀¹ r · h(r) · angularMean (lam r) dr`.
-/

open MeasureTheory Set

@[expose] public section

noncomputable section

/-- Boundary circumference `2 * π * angularMean (lam 1)` at `r = 1`. -/
def conformalBoundaryLength (lam : ℝ → ℝ → ℝ) : ℝ :=
  2 * Real.pi * angularMean (lam 1)

/-- **Lemma 1 (Unit Boundary Scale Equivalence):**
The conformal boundary length at `r = 1` is at least `2 * π` if and only if
`1 ≤ angularMean (lam 1)`. -/
theorem two_pi_le_conformalBoundaryLength_iff (lam : ℝ → ℝ → ℝ) :
    2 * Real.pi ≤ conformalBoundaryLength lam ↔ 1 ≤ angularMean (lam 1) := by
  unfold conformalBoundaryLength
  have h := mul_le_mul_iff_of_pos_left (b := 1) (c := angularMean (lam 1)) Real.two_pi_pos
  rwa [mul_one] at h

/-- **Lemma 2 (Sharp `2π` Bound from Hemisphere Moment Domination):**
If `∫₀¹ r * (hemisphereConformalFactor r) ^ 2`
is at most `∫₀¹ r * hemisphereConformalFactor r * angularMean (lam r)`,
then the conformal disk area is at least `2 * π`. -/
theorem conformal_disk_area_ge_two_pi_of_moment_ge (lam : ℝ → ℝ → ℝ)
    (hlam_cont : Continuous (Function.uncurry lam))
    (h_moment_ge :
      (∫ r in (0 : ℝ)..(1 : ℝ), r * (hemisphereConformalFactor r) ^ 2) ≤
        (∫ r in (0 : ℝ)..(1 : ℝ), r * hemisphereConformalFactor r * angularMean (lam r))) :
    2 * Real.pi ≤
      2 * Real.pi * (∫ r in (0 : ℝ)..(1 : ℝ), r * angularMean (fun θ => (lam r θ) ^ 2)) := by
  set h := hemisphereConformalFactor with hh_def
  have hh_cont : Continuous h :=
    continuous_const.div (by fun_prop) (fun r => by positivity)
  have hmean_cont : Continuous (fun r => angularMean (lam r)) :=
    continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hlam_cont _ _)
  have hA : IntervalIntegrable (fun r => r * h r * angularMean (lam r)) volume 0 1 :=
    ((continuous_id.mul hh_cont).mul hmean_cont).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun r => r * h r ^ 2) volume 0 1 :=
    (continuous_id.mul (hh_cont.pow 2)).intervalIntegrable _ _
  have h_eq : (∫ r in (0 : ℝ)..(1 : ℝ), r * h r * (angularMean (lam r) - h r)) =
      (∫ r in (0 : ℝ)..(1 : ℝ), r * h r * angularMean (lam r)) -
        ∫ r in (0 : ℝ)..(1 : ℝ), r * h r ^ 2 := by
    rw [← intervalIntegral.integral_sub hA hB]
    congr 1
    funext r
    ring
  have h_moment : 0 ≤ ∫ r in (0 : ℝ)..(1 : ℝ), r * h r * (angularMean (lam r) - h r) := by
    rw [h_eq]
    linarith
  exact conformal_disk_area_ge_two_pi_of_moment lam hlam_cont h_moment

end

end

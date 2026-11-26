/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.L2Energy
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Global Circle L² Energy Lower Bound

This file integrates the pointwise squared antipodal inequality over `[0, 2π]`
using `2π`-periodicity to prove
`π ^ 3 / 2 ≤ ∫ t in (0 : ℝ)..(2 * π), (periodicDistance F x t) ^ 2`.
-/

open MeasureTheory Metric Set

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Lemma 1 (Interval Integrability of Squared Profile):**
The squared periodic distance profile is interval-integrable on any `[a, b]`. -/
theorem periodicDistance_sq_intervalIntegrable (F : IsometricFilling M) (x : M) (a b : ℝ) :
    IntervalIntegrable (fun t => (periodicDistance F x t) ^ 2) volume a b :=
  ((periodicDistance_continuous F x).pow 2).intervalIntegrable a b

/-- Pointwise antipodal bound for the real lift: `π² / 2 ≤ f(t)² + f(t + π)²`. -/
theorem periodicDistance_antipodal_sq_sum (F : IsometricFilling M) (x : M) (t : ℝ) :
    Real.pi ^ 2 / 2 ≤
      (periodicDistance F x t) ^ 2 + (periodicDistance F x (t + Real.pi)) ^ 2 := by
  have h := kuratowski_antipodal_sq_sum F x (t : Circle2Pi)
  simpa only [periodicDistance, AddCircle.coe_add] using h

/-- Shifting by `π` maps `∫ over [0, π]` of `f(t + π)²` onto `∫ over [π, 2π]` of `f²`. -/
theorem periodicDistance_sq_integral_shift (F : IsometricFilling M) (x : M) :
    ∫ t in (0 : ℝ)..Real.pi, (periodicDistance F x (t + Real.pi)) ^ 2 =
      ∫ t in Real.pi..(2 * Real.pi), (periodicDistance F x t) ^ 2 := by
  have h := intervalIntegral.integral_comp_add_right (a := 0) (b := Real.pi)
    (fun t => (periodicDistance F x t) ^ 2) Real.pi
  rw [zero_add, show Real.pi + Real.pi = 2 * Real.pi by ring] at h
  exact h

/-- **Lemma 2 (Global L² Energy Lower Bound on `S¹`):**
For every interior point `x : M`, the `L²` norm squared of its boundary distance
profile over `[0, 2π]` is at least `π ^ 3 / 2`. -/
theorem periodicDistance_l2_lower_bound (F : IsometricFilling M) (x : M) :
    Real.pi ^ 3 / 2 ≤ ∫ t in (0 : ℝ)..(2 * Real.pi), (periodicDistance F x t) ^ 2 := by
  have hf := periodicDistance_sq_intervalIntegrable F x
  have hg : IntervalIntegrable (fun t => (periodicDistance F x (t + Real.pi)) ^ 2)
      volume 0 Real.pi :=
    (((periodicDistance_continuous F x).comp (continuous_id.add continuous_const)).pow 2
      ).intervalIntegrable 0 Real.pi
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hf 0 Real.pi)
    (hf Real.pi (2 * Real.pi))
  have hadd := intervalIntegral.integral_add (hf 0 Real.pi) hg
  have hmono := intervalIntegral.integral_mono_on Real.pi_pos.le
    (intervalIntegrable_const (c := Real.pi ^ 2 / 2)) ((hf 0 Real.pi).add hg)
    (fun t _ => periodicDistance_antipodal_sq_sum F x t)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hshift := periodicDistance_sq_integral_shift F x
  have hpi : (Real.pi - 0) * (Real.pi ^ 2 / 2) = Real.pi ^ 3 / 2 := by ring
  linarith

end

end

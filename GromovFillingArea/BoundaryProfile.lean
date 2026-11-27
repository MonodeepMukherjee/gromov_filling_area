/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.WeightedZetaBound

/-!
# Boundary Distance Profile & Tight Antipodal Equality

This file evaluates `kuratowskiMap F x` at boundary points `x = F.ι θ₀`,
proving `kuratowskiMap F (F.ι θ₀) θ = dist θ₀ θ` and establishing that the
antipodal sum bound `f_x(θ) + f_x(θ + π) = π` holds with equality on `∂M`.
-/

open MeasureTheory Metric AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Lemma 1 (Boundary Profile Reduction):**
At any boundary point `F.ι θ₀`, `kuratowskiMap F (F.ι θ₀) θ` equals `dist θ₀ θ`. -/
theorem kuratowskiMap_boundary (F : IsometricFilling M) (θ₀ θ : Circle2Pi) :
    kuratowskiMap F (F.ι θ₀) θ = dist θ₀ θ := by
  rw [kuratowskiMap]
  exact F.isometry_ι.dist_eq θ₀ θ

/-- Every point of `Circle2Pi` has a real representative in `(-π, π]`. -/
theorem circle2Pi_exists_rep_Ioc (y : Circle2Pi) :
    ∃ t ∈ Set.Ioc (-Real.pi) Real.pi, (t : Circle2Pi) = y := by
  induction y using QuotientAddGroup.induction_on with
  | H a =>
    refine ⟨toIocMod Real.two_pi_pos (-Real.pi) a, ?_, ?_⟩
    · have h := toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) a
      rwa [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h
    · rw [toIocMod, AddCircle.coe_sub, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero,
        sub_zero]

/-- On `Circle2Pi`, a real representative with `|s| ≤ π` has norm `|s|`. -/
theorem circle2Pi_norm_coe_of_abs_le (s : ℝ) (hs : |s| ≤ Real.pi) :
    ‖(s : Circle2Pi)‖ = |s| := by
  refine (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) Real.two_pi_pos.ne').mpr ?_
  rw [abs_of_pos Real.two_pi_pos]
  linarith

/-- For every `y : Circle2Pi`, the distances from `y` to `0` and to `π` sum to `π`. -/
theorem circle2Pi_norm_add_norm_sub_pi (y : Circle2Pi) :
    ‖y‖ + ‖y - (Real.pi : Circle2Pi)‖ = Real.pi := by
  obtain ⟨t, ⟨ht1, ht2⟩, rfl⟩ := circle2Pi_exists_rep_Ioc y
  have hπ := Real.pi_pos
  rw [← AddCircle.coe_sub,
    circle2Pi_norm_coe_of_abs_le t (abs_le.mpr ⟨by linarith, ht2⟩)]
  rcases le_or_gt 0 t with h0 | h0
  · rw [circle2Pi_norm_coe_of_abs_le (t - Real.pi) (abs_le.mpr ⟨by linarith, by linarith⟩),
      abs_of_nonneg h0, abs_of_nonpos (by linarith)]
    ring
  · have hshift : ((t - Real.pi : ℝ) : Circle2Pi) = ((t + Real.pi : ℝ) : Circle2Pi) := by
      rw [show t - Real.pi = (t + Real.pi) - 2 * Real.pi by ring, AddCircle.coe_sub,
        AddCircle.coe_period, sub_zero]
    rw [hshift, circle2Pi_norm_coe_of_abs_le (t + Real.pi)
        (abs_le.mpr ⟨by linarith, by linarith⟩),
      abs_of_neg h0, abs_of_pos (by linarith)]
    ring

/-- **Lemma 2 (Tight Boundary Antipodal Sum):**
For every boundary point `F.ι θ₀` and angle `θ`, the antipodal distances sum
to `π` with equality: `dist θ₀ θ + dist θ₀ (θ + π) = π`. -/
theorem circle2Pi_dist_add_antipodal (θ₀ θ : Circle2Pi) :
    dist θ₀ θ + dist θ₀ (θ + (Real.pi : Circle2Pi)) = Real.pi := by
  rw [dist_eq_norm, dist_eq_norm, ← sub_sub]
  exact circle2Pi_norm_add_norm_sub_pi (θ₀ - θ)

end

end

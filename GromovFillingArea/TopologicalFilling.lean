/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.MultiHarmonicBound

/-!
# Topological Filling & Disk Covering via Radial Retraction

This file formalizes the elementary topological disk-covering principle:
if `f : M → ℂ` maps the boundary `∂M` onto the circle `Sphere (0 : ℂ) R`
(`R > 0`) and `M` admits no continuous retraction onto its boundary circle
(the topological filling property), then `closedBall (0 : ℂ) R ⊆ range f`,
discharging the `h_fill` hypothesis in `fundamental_mode_filling_area_bound`.
-/

open MeasureTheory Metric Set BoundedContinuousFunction AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Lemma 1 (Concentric Circle Scaling on `ℂ`):**
If `R > 0` and `z : ℂ` has `‖z‖ = R`, then `(R⁻¹ : ℂ) * z` lies on the unit
circle (`‖(R⁻¹ : ℂ) * z‖ = 1`). -/
theorem norm_inv_mul_eq_one {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ = R) :
    ‖((R⁻¹ : ℝ) : ℂ) * z‖ = 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hR.le), hz,
    inv_mul_cancel₀ hR.ne']

/-- **Lemma 2 (Boundary Winding Bijection on `Sphere 0 (2 / π)`):**
The boundary map `θ₀ ↦ fourierProj 1 (kuratowskiBanach F (F.ι θ₀))` is injective
on `Circle2Pi` and lands strictly on `Metric.sphere (0 : ℂ) (2 / Real.pi)`. -/
theorem fourierProj_one_boundary_mem_sphere (F : IsometricFilling M) (θ₀ : Circle2Pi) :
    fourierProj 1 (kuratowskiBanach F (F.ι θ₀)) ∈
      Metric.sphere (0 : ℂ) (2 / Real.pi) := by
  have h := fourierProj_boundary_odd_norm F 0
  norm_num at h
  rw [mem_sphere_zero_iff_norm, fourierProj_boundary_norm F 1 θ₀]
  exact h

end

end

/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.MultiHarmonicBound

/-!
# Fundamental-Mode Boundary Circle & Radial Rescaling

This file proves two elementary facts used toward the disk-covering step:
a radial rescaling lemma (`‖z‖ = R > 0` implies `‖R⁻¹ * z‖ = 1`), and that the
fundamental Fourier projection `fourierProj 1 ∘ kuratowskiBanach F` maps every
boundary point `F.ι θ₀` onto the circle `Metric.sphere (0 : ℂ) (2 / π)`.

The disk-covering principle itself (a no-retraction / degree argument showing
`closedBall (0 : ℂ) (2 / π) ⊆ range (fourierProj 1 ∘ kuratowskiBanach F)`, which
would discharge the `h_fill` hypothesis of `fundamental_mode_filling_area_bound`)
is not formalized here.
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

/-- **Lemma 2 (Boundary Lands on `Sphere 0 (2 / π)`):**
For every boundary angle `θ₀`, the point `fourierProj 1 (kuratowskiBanach F (F.ι θ₀))`
lies on `Metric.sphere (0 : ℂ) (2 / Real.pi)`. (Injectivity and surjectivity of
this boundary map are proved in `GromovFillingArea.BoundaryWinding`.) -/
theorem fourierProj_one_boundary_mem_sphere (F : IsometricFilling M) (θ₀ : Circle2Pi) :
    fourierProj 1 (kuratowskiBanach F (F.ι θ₀)) ∈
      Metric.sphere (0 : ℂ) (2 / Real.pi) := by
  have h := fourierProj_boundary_odd_norm F 0
  norm_num at h
  rw [mem_sphere_zero_iff_norm, fourierProj_boundary_norm F 1 θ₀]
  exact h

end

end

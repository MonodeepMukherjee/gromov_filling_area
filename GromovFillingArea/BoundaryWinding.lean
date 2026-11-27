/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.TopologicalFilling

/-!
# Bijectivity of the Fundamental Boundary Winding Map

This file proves that the boundary map `θ₀ ↦ fourierProj 1 (kuratowskiBanach F (F.ι θ₀))`
is a bijection from `Circle2Pi` onto `Metric.sphere (0 : ℂ) (2 / Real.pi)`,
showing that `∂M` wraps homeomorphically once around the circle of radius `2 / π`.
-/

open MeasureTheory Metric Set BoundedContinuousFunction AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The base coefficient `fourierProj 1 (kuratowskiBanach F (F.ι 0))` is nonzero
(its norm is `2 / π > 0`). -/
theorem fourierProj_one_base_ne_zero (F : IsometricFilling M) :
    fourierProj 1 (kuratowskiBanach F (F.ι 0)) ≠ 0 := by
  have h := mem_sphere_zero_iff_norm.mp (fourierProj_one_boundary_mem_sphere F 0)
  intro h0
  rw [h0, norm_zero] at h
  exact (div_pos two_pos Real.pi_pos).ne h

/-- **Lemma 1 (Injectivity of the Fundamental Boundary Map):**
Distinct boundary angles `θ₁ ≠ θ₂` in `Circle2Pi` map to distinct points on
`Metric.sphere (0 : ℂ) (2 / Real.pi)` under `fourierProj 1 ∘ kuratowskiBanach F ∘ F.ι`. -/
theorem fourierProj_one_boundary_injective (F : IsometricFilling M) :
    Function.Injective (fun θ₀ : Circle2Pi =>
      fourierProj 1 (kuratowskiBanach F (F.ι θ₀))) := by
  intro θ₁ θ₂ h
  simp only at h
  rw [fourierProj_boundary_eq F 1 θ₁, fourierProj_boundary_eq F 1 θ₂] at h
  have h' := mul_right_cancel₀ (fourierProj_one_base_ne_zero F) h
  rw [fourier_apply, fourier_apply, neg_one_zsmul, neg_one_zsmul] at h'
  exact neg_inj.mp (injective_toCircle Real.two_pi_pos.ne' (Circle.coe_injective h'))

/-- **Lemma 2 (Surjectivity onto `Sphere 0 (2 / π)`):**
Every point `w` on `Metric.sphere (0 : ℂ) (2 / Real.pi)` is attained by
`fourierProj 1 (kuratowskiBanach F (F.ι θ₀))` for some `θ₀ : Circle2Pi`. -/
theorem fourierProj_one_boundary_surjective (F : IsometricFilling M)
    {w : ℂ} (hw : w ∈ Metric.sphere (0 : ℂ) (2 / Real.pi)) :
    ∃ θ₀ : Circle2Pi, fourierProj 1 (kuratowskiBanach F (F.ι θ₀)) = w := by
  have hc := fourierProj_one_base_ne_zero F
  have hcn := mem_sphere_zero_iff_norm.mp (fourierProj_one_boundary_mem_sphere F 0)
  have hwn := mem_sphere_zero_iff_norm.mp hw
  have hu : ‖w / fourierProj 1 (kuratowskiBanach F (F.ι 0))‖ = 1 := by
    rw [norm_div, hwn, hcn, div_self (div_pos two_pos Real.pi_pos).ne']
  have hexp : Complex.exp
      (Complex.arg (w / fourierProj 1 (kuratowskiBanach F (F.ι 0))) * Complex.I) =
        w / fourierProj 1 (kuratowskiBanach F (F.ι 0)) := by
    have h := Complex.norm_mul_exp_arg_mul_I (w / fourierProj 1 (kuratowskiBanach F (F.ι 0)))
    rwa [hu, Complex.ofReal_one, one_mul] at h
  refine ⟨((-Complex.arg (w / fourierProj 1 (kuratowskiBanach F (F.ι 0))) : ℝ) : Circle2Pi),
    ?_⟩
  rw [fourierProj_boundary_eq F 1, fourier_neg_coe_eq_cexp]
  have harg : -((1 : ℤ) : ℂ) * Complex.I *
      ((-Complex.arg (w / fourierProj 1 (kuratowskiBanach F (F.ι 0))) : ℝ) : ℂ) =
        Complex.arg (w / fourierProj 1 (kuratowskiBanach F (F.ι 0))) * Complex.I := by
    push_cast
    ring
  rw [harg, hexp, div_mul_cancel₀ w hc]

end

end

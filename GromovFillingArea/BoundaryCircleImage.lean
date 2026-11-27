/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.FourierProjection

/-!
# Rotational Equivariance & Circular Boundary Image in `ℂ`

This file proves that for every frequency `n : ℤ`, the `n`-th Fourier projection
maps boundary points `F.ι θ₀` equivariantly via `fourier (-n) θ₀`, so the
boundary `∂M` lands on a circle of constant radius `‖f̂_{ι 0}(n)‖` in `ℂ`.
-/

open MeasureTheory Metric Set BoundedContinuousFunction AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The boundary profile at `F.ι θ₀` is the profile at `F.ι 0` translated by `-θ₀`. -/
theorem kuratowskiMap_boundary_shift (F : IsometricFilling M) (θ₀ θ : Circle2Pi) :
    kuratowskiMap F (F.ι θ₀) θ = kuratowskiMap F (F.ι 0) (θ + -θ₀) := by
  rw [kuratowskiMap_boundary, kuratowskiMap_boundary, dist_eq_norm, dist_eq_norm,
    show (0 : Circle2Pi) - (θ + -θ₀) = θ₀ - θ by abel]

/-- Every character value `fourier n θ` has modulus `1`. -/
theorem fourier_norm_apply (n : ℤ) (θ : Circle2Pi) : ‖fourier n θ‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

/-- **Lemma 1 (Boundary Rotational Equivariance of Fourier Projections):**
Evaluating `fourierProj n` at the boundary point `F.ι θ₀` rotates the base
coefficient at `F.ι 0` by the unitary character `fourier (-n) θ₀`. -/
theorem fourierProj_boundary_eq (F : IsometricFilling M) (n : ℤ) (θ₀ : Circle2Pi) :
    fourierProj n (kuratowskiBanach F (F.ι θ₀)) =
      fourier (-n) θ₀ * fourierProj n (kuratowskiBanach F (F.ι 0)) := by
  induction θ₀ using QuotientAddGroup.induction_on with
  | H t =>
    have key := fourierCoeff_add_shift
      (fun u : Circle2Pi => ((kuratowskiBanach F (F.ι 0)) u : ℂ)) n (-t)
    rw [AddCircle.coe_neg, neg_neg] at key
    simp only [fourierProj]
    rw [← key]
    congr 1
    funext θ
    simp only [kuratowskiBanach_apply]
    rw [kuratowskiMap_boundary_shift]

/-- **Lemma 2 (Constant Modulus on the Boundary Circle):**
Every boundary point `F.ι θ₀` maps under `fourierProj n ∘ kuratowskiBanach F`
to the circle of radius `‖fourierProj n (kuratowskiBanach F (F.ι 0))‖` in `ℂ`. -/
theorem fourierProj_boundary_norm (F : IsometricFilling M) (n : ℤ) (θ₀ : Circle2Pi) :
    ‖fourierProj n (kuratowskiBanach F (F.ι θ₀))‖ =
      ‖fourierProj n (kuratowskiBanach F (F.ι 0))‖ := by
  rw [fourierProj_boundary_eq, norm_mul, fourier_norm_apply, one_mul]

end

end

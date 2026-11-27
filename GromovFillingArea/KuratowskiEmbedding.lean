/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.BoundaryProfile
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Kuratowski Banach-Space Embedding `M → (Circle2Pi →ᵇ ℝ)`

This file packages the distance profile `x ↦ (θ ↦ dist x (F.ι θ))` as a map
into the Banach space `Circle2Pi →ᵇ ℝ` of bounded continuous functions on `S¹`
with the supremum norm, and proves `LipschitzWith 1` on `M` (which governs
`2`-dimensional Hausdorff area contraction).
-/

open MeasureTheory Metric BoundedContinuousFunction

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The Kuratowski map sending `x : M` to its boundary distance profile in `Circle2Pi →ᵇ ℝ`. -/
def kuratowskiBanach (F : IsometricFilling M) (x : M) : Circle2Pi →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨kuratowskiMap F x, (kuratowskiMap_lipschitzWith F x).continuous⟩

/-- Evaluating `kuratowskiBanach F x` at `θ` recovers `kuratowskiMap F x θ`. -/
theorem kuratowskiBanach_apply (F : IsometricFilling M) (x : M) (θ : Circle2Pi) :
    kuratowskiBanach F x θ = kuratowskiMap F x θ :=
  rfl

/-- **Lemma 1 (Global 1-Lipschitz Contraction into `L^∞(S¹)`):**
The Kuratowski embedding `kuratowskiBanach F : M → (Circle2Pi →ᵇ ℝ)` is `1`-Lipschitz
with respect to the supremum norm. -/
theorem kuratowskiBanach_lipschitzWith (F : IsometricFilling M) :
    LipschitzWith 1 (kuratowskiBanach F) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul]
  refine (BoundedContinuousFunction.dist_le dist_nonneg).mpr fun θ => ?_
  rw [kuratowskiBanach_apply, kuratowskiBanach_apply, Real.dist_eq]
  exact kuratowski_nonexpansive F x y θ

/-- **Lemma 2 (Exact Boundary Isometry into `L^∞(S¹)`):**
On the boundary `F.ι '' univ`, `kuratowskiBanach F` preserves distances with equality:
`dist (kuratowskiBanach F (F.ι θ₁)) (kuratowskiBanach F (F.ι θ₂)) = dist θ₁ θ₂`. -/
theorem kuratowskiBanach_boundary_isometry (F : IsometricFilling M) (θ₁ θ₂ : Circle2Pi) :
    dist (kuratowskiBanach F (F.ι θ₁)) (kuratowskiBanach F (F.ι θ₂)) = dist θ₁ θ₂ := by
  refine le_antisymm ?_ ?_
  · have h := (kuratowskiBanach_lipschitzWith F).dist_le_mul (F.ι θ₁) (F.ι θ₂)
    rwa [NNReal.coe_one, one_mul, F.isometry_ι.dist_eq] at h
  · have h := BoundedContinuousFunction.dist_coe_le_dist
      (f := kuratowskiBanach F (F.ι θ₁)) (g := kuratowskiBanach F (F.ι θ₂)) θ₂
    rwa [kuratowskiBanach_apply, kuratowskiBanach_apply, kuratowskiMap_boundary,
      kuratowskiMap_boundary, dist_self, Real.dist_eq, sub_zero,
      abs_of_nonneg dist_nonneg] at h

end

end

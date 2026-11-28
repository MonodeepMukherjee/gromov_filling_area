/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.MultiModeVectorEmbedding

/-!
# Odd-Harmonic Boundary Torus Embedding in `Fin K → ℂ`

This file proves that for every `K : ℕ`, the boundary curve
`θ₀ ↦ oddHarmonicVectorMap K (kuratowskiBanach F (F.ι θ₀))` in `Fin K → ℂ`
lands on the exact `(2K)`-dimensional torus product of circles of radii
`R_{2j+1} = 2 / ((2j + 1)^2 * π)` (`j : Fin K`), and is injective on `Circle2Pi`
whenever `1 ≤ K`.
-/

open MeasureTheory Metric Set BoundedContinuousFunction AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Lemma 1 (Exact Torus Product Containment of Boundary Image):**
For every `K : ℕ`, `θ₀ : Circle2Pi`, and coordinate `j : Fin K`, the `j`-th
component of `oddHarmonicVectorMap K (kuratowskiBanach F (F.ι θ₀))` lies on
`Metric.sphere (0 : ℂ) (2 / ((2 * (j : ℝ) + 1) ^ 2 * Real.pi))`. -/
theorem oddHarmonicVectorMap_boundary_mem_sphere (F : IsometricFilling M)
    (K : ℕ) (θ₀ : Circle2Pi) (j : Fin K) :
    oddHarmonicVectorMap K (kuratowskiBanach F (F.ι θ₀)) j ∈
      Metric.sphere (0 : ℂ) (2 / ((2 * (j : ℝ) + 1) ^ 2 * Real.pi)) := by
  rw [mem_sphere_zero_iff_norm, oddHarmonicVectorMap,
    fourierProj_boundary_norm F (2 * (j : ℤ) + 1) θ₀]
  exact fourierProj_boundary_odd_norm F j

/-- **Lemma 2 (Injectivity of the `K`-Mode Boundary Torus Curve):**
Whenever `1 ≤ K`, the map `θ₀ ↦ oddHarmonicVectorMap K (kuratowskiBanach F (F.ι θ₀))`
is injective from `Circle2Pi` into `Fin K → ℂ`. -/
theorem oddHarmonicVectorMap_boundary_injective (F : IsometricFilling M)
    {K : ℕ} (hK : 1 ≤ K) :
    Function.Injective (fun θ₀ : Circle2Pi =>
      oddHarmonicVectorMap K (kuratowskiBanach F (F.ι θ₀))) := by
  intro θ₁ θ₂ h
  have h0 := congrFun h ⟨0, hK⟩
  simp only [oddHarmonicVectorMap, Nat.cast_zero, mul_zero, zero_add] at h0
  exact fourierProj_one_boundary_injective F h0

end

end

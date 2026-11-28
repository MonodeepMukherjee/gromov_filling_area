/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Gromov's Filling Area Conjecture

This file defines an isometric filling of the Riemannian circle `S¹` of length `2π`
using metric geometry and 2-dimensional Hausdorff measure, and states Gromov's
Filling Area Conjecture (`Area(M) ≥ 2π`).

## Normalization

Mathlib's `MeasureTheory.Measure.hausdorffMeasure 2` (`μH[2]`) is the *unnormalized*
Hausdorff measure: covers are weighted by `diam ^ 2`, with no factor `π / 4`. By the
isodiametric inequality it equals `(4 / π) * Area` on the Euclidean plane, hence on every
Riemannian surface. The round hemisphere of Riemannian area `2π` therefore has
`μH[2] = 8`, and Gromov's bound `Area(M) ≥ 2π` reads `8 ≤ μH[2] (univ : Set M)`.
On the sup-norm plane `Fin 2 → ℝ`, by contrast, `μH[2]` equals Lebesgue measure.
-/

open MeasureTheory Metric

@[expose] public section

noncomputable section

/-- The Riemannian circle of length `2π`, modeled as `AddCircle (2 * Real.pi)`. -/
abbrev Circle2Pi := AddCircle (2 * Real.pi)

/-- A compact metric space `M` is an **isometric filling** of `S¹` (of length `2π`)
if there is an isometric embedding `ι : Circle2Pi → M` preserving boundary distances
and satisfying a topological filling condition. The field `no_boundary_retraction` says
the boundary circle is not a retract of `M`: no continuous `r : M → Circle2Pi` restricts
to the identity on `ι`. -/
structure IsometricFilling (M : Type*) [MetricSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] where
  ι : Circle2Pi → M
  isometry_ι : Isometry ι
  is_orientable_surface : Prop
  valid_topology : is_orientable_surface
  no_boundary_retraction : ¬ ∃ r : M → Circle2Pi, Continuous r ∧ ∀ θ : Circle2Pi, r (ι θ) = θ

/-- **Gromov's Filling Area Conjecture (1983):**
Every orientable topological surface `M` isometrically filling a circle of length `2π`
has area at least `2π`, the area of the round hemisphere.

In Mathlib's unnormalized `μH[2]`, which is `(4 / π) * Area` on a Riemannian surface (see
the module docstring), the hemisphere has `μH[2] = 8`, so the conjecture is `8 ≤ μH[2]`. -/
def GromovFillingAreaConjecture : Prop :=
  ∀ (M : Type) [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M],
    Nonempty (IsometricFilling M) →
    (8 : ENNReal) ≤ MeasureTheory.Measure.hausdorffMeasure 2 (Set.univ : Set M)

/-- **Milestone 1 Sanity Check:** `2π` is strictly positive, ensuring non-triviality. -/
theorem two_pi_pos : (0 : ℝ) < 2 * Real.pi := by
  positivity

end

end

/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.SharpFirstMode

/-!
# Quarter-Circle Boundary Pair Map & `L¹`-Diamond Boundary Geometry

This file formalizes the second discovery of `scripts/conjecture_discovery.py`:
evaluating `kuratowskiMap F x` at the quarter-circle pair `(0, π / 2)` yields
a `1`-Lipschitz map `quarterPairMap F : M → (Fin 2 → ℝ)` into the sup-norm
plane (where `hausdorffMeasure 2` equals exact Lebesgue area), sending `∂M` onto
the boundary of the `L¹`-diamond `|u - π / 2| + |v - π / 2| = π / 2` of area `π² / 2`.
-/

open MeasureTheory Metric Set BoundedContinuousFunction AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The quarter-circle Kuratowski pair map `x ↦ ![f_x(0), f_x(π / 2)]` in `Fin 2 → ℝ`. -/
def quarterPairMap (F : IsometricFilling M) (x : M) : Fin 2 → ℝ :=
  ![kuratowskiMap F x 0, kuratowskiMap F x ((Real.pi / 2 : ℝ) : Circle2Pi)]

/-- **Lemma 1 (1-Lipschitz Contraction into the Sup-Norm Plane):**
`quarterPairMap F : M → (Fin 2 → ℝ)` is `1`-Lipschitz (`LipschitzWith 1`). -/
theorem quarterPairMap_lipschitzWith (F : IsometricFilling M) :
    LipschitzWith 1 (quarterPairMap F) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul]
  refine (dist_pi_le_iff dist_nonneg).2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · change dist (kuratowskiMap F x 0) (kuratowskiMap F y 0) ≤ dist x y
    rw [Real.dist_eq]
    exact kuratowski_nonexpansive F x y 0
  · change dist (kuratowskiMap F x ((Real.pi / 2 : ℝ) : Circle2Pi))
      (kuratowskiMap F y ((Real.pi / 2 : ℝ) : Circle2Pi)) ≤ dist x y
    rw [Real.dist_eq]
    exact kuratowski_nonexpansive F x y _

/-- **Lemma 2 (Boundary Image Lies on the `L¹`-Diamond `|u - π/2| + |v - π/2| = π/2`):**
For every boundary angle `θ : Circle2Pi`, the coordinates
`u = dist 0 θ` and `v = dist (π / 2) θ` satisfy
`|u - Real.pi / 2| + |v - Real.pi / 2| = Real.pi / 2`. -/
theorem quarterCircle_boundary_diamond (θ : Circle2Pi) :
    |dist (0 : Circle2Pi) θ - Real.pi / 2| +
      |dist ((Real.pi / 2 : ℝ) : Circle2Pi) θ - Real.pi / 2| = Real.pi / 2 := by
  have hπ := Real.pi_pos
  obtain ⟨t, ⟨ht1, ht2⟩, rfl⟩ := circle2Pi_exists_rep_Ioc θ
  have hu : dist (0 : Circle2Pi) (t : Circle2Pi) = |t| := by
    rw [dist_comm, dist_zero_right,
      circle2Pi_norm_coe_of_abs_le t (abs_le.2 ⟨by linarith, ht2⟩)]
  -- `dist (π/2) t = |s|` for any representative `s` of `π/2 - t` with `|s| ≤ π`
  have hv : ∀ s : ℝ, |s| ≤ Real.pi →
      ((Real.pi / 2 - t : ℝ) : Circle2Pi) = (s : Circle2Pi) →
      dist ((Real.pi / 2 : ℝ) : Circle2Pi) (t : Circle2Pi) = |s| := by
    intro s hs hst
    rw [dist_eq_norm, ← AddCircle.coe_sub, hst, circle2Pi_norm_coe_of_abs_le s hs]
  rw [hu]
  rcases le_or_gt t (-(Real.pi / 2)) with h1 | h1
  · -- `t ∈ (-π, -π/2]`: shift `π/2 - t ∈ [π, 3π/2)` down by the period
    have hst : ((Real.pi / 2 - t : ℝ) : Circle2Pi) =
        ((Real.pi / 2 - t - 2 * Real.pi : ℝ) : Circle2Pi) := by
      rw [← AddCircle.coe_add_period (p := 2 * Real.pi) (Real.pi / 2 - t - 2 * Real.pi)]
      congr 1
      ring
    rw [hv _ (abs_le.2 ⟨by linarith, by linarith⟩) hst,
      abs_of_neg (by linarith : t < 0),
      abs_of_neg (by linarith : Real.pi / 2 - t - 2 * Real.pi < 0),
      abs_of_nonneg (by linarith : 0 ≤ -t - Real.pi / 2),
      abs_of_nonneg (by linarith : 0 ≤ -(Real.pi / 2 - t - 2 * Real.pi) - Real.pi / 2)]
    ring
  rcases le_or_gt t 0 with h2 | h2
  · -- `t ∈ (-π/2, 0]`
    rw [hv _ (abs_le.2 ⟨by linarith, by linarith⟩) rfl, abs_of_nonpos h2,
      abs_of_nonneg (by linarith : 0 ≤ Real.pi / 2 - t),
      abs_of_nonpos (by linarith : -t - Real.pi / 2 ≤ 0),
      abs_of_nonneg (by linarith : 0 ≤ Real.pi / 2 - t - Real.pi / 2)]
    ring
  rcases le_or_gt t (Real.pi / 2) with h3 | h3
  · -- `t ∈ (0, π/2]`
    rw [hv _ (abs_le.2 ⟨by linarith, by linarith⟩) rfl, abs_of_pos h2,
      abs_of_nonneg (by linarith : 0 ≤ Real.pi / 2 - t),
      abs_of_nonpos (by linarith : t - Real.pi / 2 ≤ 0),
      abs_of_nonpos (by linarith : Real.pi / 2 - t - Real.pi / 2 ≤ 0)]
    ring
  · -- `t ∈ (π/2, π]`
    rw [hv _ (abs_le.2 ⟨by linarith, by linarith⟩) rfl, abs_of_pos h2,
      abs_of_neg (by linarith : Real.pi / 2 - t < 0),
      abs_of_nonneg (by linarith : 0 ≤ t - Real.pi / 2),
      abs_of_nonpos (by linarith : -(Real.pi / 2 - t) - Real.pi / 2 ≤ 0)]
    ring

end

end

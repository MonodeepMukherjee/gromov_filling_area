/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.Basic

/-!
# Non-Vacuity & Isometric Embedding Witnesses

This file proves that the isometric embedding condition `Isometry ι` in
`IsometricFilling` is satisfiable (non-vacuous) by constructing explicit
isometric embeddings of `Circle2Pi`.
-/

open MeasureTheory Metric

@[expose] public section

noncomputable section

/-- **Lemma 1 (Identity Boundary Witness):**
`Circle2Pi` isometrically embeds into itself via `id`, confirming `Isometry ι`
is non-vacuous and compact. -/
theorem circle2Pi_self_isometry : Isometry (id : Circle2Pi → Circle2Pi) :=
  isometry_id

/-- **Lemma 2 (Diameter Upper Bound on `Circle2Pi`):**
Any two points on `Circle2Pi` are at distance at most `π`. -/
theorem circle2Pi_dist_le_pi (θ₁ θ₂ : Circle2Pi) :
    dist θ₁ θ₂ ≤ Real.pi := by
  have h := AddCircle.norm_le_half_period (2 * Real.pi) (x := θ₁ - θ₂) Real.two_pi_pos.ne'
  rw [abs_of_pos Real.two_pi_pos] at h
  rw [dist_eq_norm]
  linarith

end

end

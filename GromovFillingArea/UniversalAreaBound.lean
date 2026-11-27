/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.DiskCovering

/-!
# End-to-End Universal Filling Area Lower Bound (`4 / π`)

This file packages the fundamental boundary winding bijection as a homeomorphism
`Circle2Pi ≃ₜ Metric.sphere (0 : ℂ) (2 / Real.pi)` and discharges `h_fill` via
`disk_covered_of_no_retraction`, yielding the unconditional universal lower bound
`ENNReal.ofReal (4 / Real.pi) ≤ hausdorffMeasure 2 (univ : Set M)`.
-/

open MeasureTheory Metric Set BoundedContinuousFunction AddCircle Topology

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Definition 1 (Fundamental Boundary Winding Homeomorphism):**
Because `Circle2Pi` is compact and `Metric.sphere (0 : ℂ) (2 / Real.pi)` is Hausdorff,
the continuous bijection `θ₀ ↦ fourierProj 1 (kuratowskiBanach F (F.ι θ₀))` is a
homeomorphism `Circle2Pi ≃ₜ Metric.sphere (0 : ℂ) (2 / Real.pi)`. -/
def fourierProjOneBoundaryHomeomorph (F : IsometricFilling M) :
    Circle2Pi ≃ₜ Metric.sphere (0 : ℂ) (2 / Real.pi) :=
  let g : Circle2Pi → Metric.sphere (0 : ℂ) (2 / Real.pi) := fun θ₀ =>
    ⟨fourierProj 1 (kuratowskiBanach F (F.ι θ₀)),
      fourierProj_one_boundary_mem_sphere F θ₀⟩
  have hg_cont : Continuous g := by
    refine Continuous.subtype_mk ?_ _
    exact (fourierProj_lipschitzWith 1).continuous.comp
      ((kuratowskiBanach_lipschitzWith F).continuous.comp F.isometry_ι.continuous)
  have hg_bij : Function.Bijective g := by
    refine ⟨?_, ?_⟩
    · intro θ₁ θ₂ h
      exact fourierProj_one_boundary_injective F (congrArg Subtype.val h)
    · rintro ⟨w, hw⟩
      obtain ⟨θ₀, rfl⟩ := fourierProj_one_boundary_surjective F hw
      exact ⟨θ₀, rfl⟩
  hg_cont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hg_bij)

/-- **Main Theorem (Gromov's Universal `4 / π` Filling Area Lower Bound):**
Every isometric filling `F : IsometricFilling M` has `2`-dimensional Hausdorff area at
least `ENNReal.ofReal (4 / Real.pi)`. The boundary non-retraction condition is supplied by
the structure field `F.no_boundary_retraction`. -/
theorem gromov_universal_four_div_pi_bound (F : IsometricFilling M) :
    ENNReal.ofReal (4 / Real.pi) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) := by
  have hcont : Continuous (fourierProj 1 ∘ kuratowskiBanach F) :=
    (fourierProj_lipschitzWith 1).continuous.comp (kuratowskiBanach_lipschitzWith F).continuous
  exact fundamental_mode_filling_area_bound F
    (disk_covered_of_no_retraction F (by positivity) (fourierProj 1 ∘ kuratowskiBanach F)
      hcont (fourierProjOneBoundaryHomeomorph F) (fun _ => rfl) F.no_boundary_retraction)

end

end

/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.RadialRetraction

/-!
# Continuity of Radial Projection & Topological Disk Covering

This file proves that `radialProj p R` is continuous away from `p`
(`ContinuousOn (radialProj p R) {z | z ≠ p}`) and formalizes the topological
disk-covering theorem: if a continuous map `f : M → ℂ` restricts via `F.ι` to a
homeomorphism `Circle2Pi ≃ₜ Metric.sphere (0 : ℂ) R` and `M` admits no continuous
retraction onto `Circle2Pi`, then `Metric.closedBall (0 : ℂ) R ⊆ range f`.
-/

open MeasureTheory Metric Set Complex Topology

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Lemma 1 (Continuity of Radial Ray Projection Away from `p`):**
For any `p : ℂ` and `R : ℝ`, `radialProj p R` is continuous on `{z : ℂ | z ≠ p}`. -/
theorem radialProj_continuousOn (p : ℂ) (R : ℝ) :
    ContinuousOn (radialProj p R) {z : ℂ | z ≠ p} := by
  have hd : Continuous (fun z : ℂ => z - p) := continuous_id.sub continuous_const
  have ha : Continuous (fun z : ℂ => Complex.normSq (z - p)) := continuous_normSq.comp hd
  have hb : Continuous (fun z : ℂ => (p * starRingEnd ℂ (z - p)).re) :=
    continuous_re.comp (continuous_const.mul (continuous_conj.comp hd))
  have hnum : Continuous (fun z : ℂ => -(p * starRingEnd ℂ (z - p)).re +
      Real.sqrt ((p * starRingEnd ℂ (z - p)).re ^ 2 -
        Complex.normSq (z - p) * (Complex.normSq p - R ^ 2))) :=
    hb.neg.add ((hb.pow 2).sub (ha.mul continuous_const)).sqrt
  have hparam : ContinuousOn (fun z : ℂ => radialRayParam p R z) {z : ℂ | z ≠ p} :=
    hnum.continuousOn.div ha.continuousOn
      (fun z hz => (Complex.normSq_pos.mpr (sub_ne_zero.mpr hz)).ne')
  exact continuousOn_const.add
    ((continuous_ofReal.comp_continuousOn hparam).mul hd.continuousOn)

/-- **Lemma 2 (Topological Disk Covering via No-Retraction):**
If `f : M → ℂ` is continuous, restricts along `F.ι` to a homeomorphism
`e : Circle2Pi ≃ₜ Metric.sphere (0 : ℂ) R` (`R > 0`), and `M` admits no continuous
retraction `r : M → Circle2Pi` (`∀ θ, r (F.ι θ) = θ`), then
`Metric.closedBall (0 : ℂ) R ⊆ range f`. -/
theorem disk_covered_of_no_retraction (F : IsometricFilling M) {R : ℝ} (hR : 0 < R)
    (f : M → ℂ) (hf : Continuous f)
    (e : Circle2Pi ≃ₜ Metric.sphere (0 : ℂ) R)
    (he : ∀ θ : Circle2Pi, (e θ : ℂ) = f (F.ι θ))
    (h_no_retract : ¬ ∃ r : M → Circle2Pi, Continuous r ∧ ∀ θ : Circle2Pi, r (F.ι θ) = θ) :
    Metric.closedBall (0 : ℂ) R ⊆ range f := by
  intro w hw
  by_contra hmissw
  rw [mem_closedBall, dist_zero_right] at hw
  rcases hw.lt_or_eq with hlt | heq
  · -- interior point missed: radial projection from `w` gives a forbidden retraction
    have hmiss : ∀ x, f x ≠ w := fun x hx => hmissw ⟨x, hx⟩
    have hrc : Continuous (fun x => radialProj w R (f x)) :=
      (radialProj_continuousOn w R).comp_continuous hf hmiss
    refine h_no_retract ⟨fun x => e.symm ⟨radialProj w R (f x),
      radialProj_mem_sphere hR hlt (hmiss x)⟩, e.symm.continuous.comp (hrc.subtype_mk _),
      fun θ => ?_⟩
    have hmem : f (F.ι θ) ∈ Metric.sphere (0 : ℂ) R := by
      rw [← he θ]
      exact (e θ).2
    have hfix : (⟨radialProj w R (f (F.ι θ)), radialProj_mem_sphere hR hlt (hmiss _)⟩ :
        Metric.sphere (0 : ℂ) R) = e θ :=
      Subtype.ext (by
        change radialProj w R (f (F.ι θ)) = (e θ : ℂ)
        rw [radialProj_eq_self_of_mem_sphere hR hlt hmem, he θ])
    change e.symm ⟨radialProj w R (f (F.ι θ)), _⟩ = θ
    rw [hfix, Homeomorph.symm_apply_apply]
  · -- boundary point: hit directly by the boundary homeomorphism
    apply hmissw
    refine ⟨F.ι (e.symm ⟨w, mem_sphere_zero_iff_norm.mpr heq⟩), ?_⟩
    rw [← he, Homeomorph.apply_symm_apply]

end

end

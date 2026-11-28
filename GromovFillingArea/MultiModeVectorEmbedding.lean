/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.CalibrationPullback

/-!
# Higher-Dimensional Odd-Harmonic Vector Embedding `(Circle2Pi →ᵇ ℝ) → (Fin K → ℂ)`

To escape the `π² / 2` ceiling of `2`-dimensional planar projections, this file
defines the `K`-mode odd-harmonic vector map
`oddHarmonicVectorMap K : (Circle2Pi →ᵇ ℝ) → (Fin K → ℂ)`
sending `g ↦ fun j : Fin K => fourierProj (2 * (j : ℤ) + 1) g` (equipped with the
`L^∞` sup-metric on `Fin K → ℂ`). It proves `LipschitzWith 1` and deduces that
the `2`-dimensional Hausdorff area of its image in `Fin K → ℂ` is at most
`hausdorffMeasure 2 (univ : Set M)`.
-/

open MeasureTheory Metric Set BoundedContinuousFunction AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The `K`-mode odd-harmonic vector map `g ↦ (f̂(1), f̂(3), ..., f̂(2K-1))` into `Fin K → ℂ`. -/
def oddHarmonicVectorMap (K : ℕ) (g : Circle2Pi →ᵇ ℝ) : Fin K → ℂ :=
  fun j : Fin K => fourierProj (2 * (j : ℤ) + 1) g

/-- **Lemma 1 (1-Lipschitz Property of `oddHarmonicVectorMap K`):**
With the `L^∞` sup-metric on `Fin K → ℂ`, `oddHarmonicVectorMap K` is `1`-Lipschitz. -/
theorem oddHarmonicVectorMap_lipschitzWith (K : ℕ) :
    LipschitzWith 1 (oddHarmonicVectorMap K) := by
  refine LipschitzWith.of_dist_le_mul fun g h => ?_
  rw [NNReal.coe_one, one_mul]
  refine (dist_pi_le_iff dist_nonneg).2 fun j => ?_
  simpa [oddHarmonicVectorMap] using
    (fourierProj_lipschitzWith (2 * (j : ℤ) + 1)).dist_le_mul g h

/-- **Lemma 2 (Higher-Dimensional Odd-Harmonic Area Contraction):**
For every `F : IsometricFilling M` and every `K : ℕ`, the `2`-dimensional Hausdorff
measure of `range (oddHarmonicVectorMap K ∘ kuratowskiBanach F)` in `Fin K → ℂ`
is bounded above by `hausdorffMeasure 2 (univ : Set M)`. -/
theorem kuratowski_oddHarmonicVectorMap_hausdorffMeasure_le (F : IsometricFilling M) (K : ℕ) :
    MeasureTheory.Measure.hausdorffMeasure 2
        (range (oddHarmonicVectorMap K ∘ kuratowskiBanach F)) ≤
      MeasureTheory.Measure.hausdorffMeasure 2 (univ : Set M) :=
  kuratowskiBanach_proj_hausdorffMeasure_le F (oddHarmonicVectorMap K)
    (oddHarmonicVectorMap_lipschitzWith K)

end

end

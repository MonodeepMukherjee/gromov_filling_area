/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.IntegralBound
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Parseval Fourier Identity for Kuratowski Distance Profiles

This file proves continuity and `L²` membership (`MemLp · 2 haarAddCircle`) of the
complexified Kuratowski distance profile on `Circle2Pi` and establishes Parseval's
Fourier coefficient series identity via `hasSum_sq_fourierCoeff`.
-/

open MeasureTheory Metric AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The period `2π` of `Circle2Pi` is positive; needed for `haarAddCircle`. -/
instance Circle2Pi.fact_two_pi_pos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Complex-valued Kuratowski distance profile on `Circle2Pi` for Fourier expansion. -/
def kuratowskiComplex (F : IsometricFilling M) (x : M) (θ : Circle2Pi) : ℂ :=
  (kuratowskiMap F x θ : ℂ)

/-- The complexified Kuratowski profile is continuous on `Circle2Pi`. -/
theorem kuratowskiComplex_continuous (F : IsometricFilling M) (x : M) :
    Continuous (kuratowskiComplex F x) :=
  Complex.continuous_ofReal.comp (kuratowskiMap_lipschitzWith F x).continuous

/-- **Lemma 1 (`L²` Membership on `Circle2Pi`):**
Because `kuratowskiMap F x` is 1-Lipschitz on compact `Circle2Pi`, its complex
lift belongs to `Lp` with exponent `2` under `haarAddCircle`. -/
theorem kuratowskiComplex_memLp (F : IsometricFilling M) (x : M) :
    MemLp (kuratowskiComplex F x) 2 haarAddCircle :=
  (kuratowskiComplex_continuous F x).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- **Lemma 2 (Parseval Fourier Coefficient Series):**
The `L²` norm squared of `kuratowskiComplex F x` under `haarAddCircle` equals
the infinite sum of squared magnitudes of its Fourier coefficients. -/
theorem kuratowski_parseval_hasSum (F : IsometricFilling M) (x : M) :
    HasSum (fun n : ℤ => ‖fourierCoeff (kuratowskiComplex F x) n‖ ^ 2)
      (∫ θ : Circle2Pi, ‖kuratowskiComplex F x θ‖ ^ 2 ∂haarAddCircle) := by
  have hL := kuratowskiComplex_memLp F x
  convert hasSum_sq_fourierCoeff hL.toLp using 1
  · ext n
    rw [fourierCoeff_congr_ae hL.coeFn_toLp]
  · exact integral_congr_ae (hL.coeFn_toLp.mono fun t ht => by simp only [ht])

end

end

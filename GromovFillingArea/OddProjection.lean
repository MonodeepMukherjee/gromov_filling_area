/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.FourierShift

/-!
# Odd-Harmonic Doubling & Spectral Projection

This file proves that for every odd index `2 * k + 1`, the Fourier coefficient
of the antipodal difference profile `antipodalDiff F x` doubles the corresponding
coefficient of `kuratowskiComplex F x`, and establishes Parseval's identity
for `antipodalDiff F x`.
-/

open MeasureTheory Metric AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- A continuous function on `Circle2Pi`, twisted by a character, is Haar-integrable. -/
theorem fourier_smul_integrable (g : Circle2Pi → ℂ) (hg : Continuous g) (n : ℤ) :
    Integrable (fun t : Circle2Pi => fourier n t • g t) haarAddCircle :=
  ((fourier n).continuous.smul hg).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- `fourierCoeff` is additive with respect to pointwise subtraction of continuous maps. -/
theorem fourierCoeff_sub_of_continuous (f g : Circle2Pi → ℂ) (hf : Continuous f)
    (hg : Continuous g) (n : ℤ) :
    fourierCoeff (fun θ => f θ - g θ) n = fourierCoeff f n - fourierCoeff g n := by
  simp only [fourierCoeff, smul_sub]
  exact integral_sub (fourier_smul_integrable f hf (-n)) (fourier_smul_integrable g hg (-n))

/-- The half-period shift of the complexified profile is continuous. -/
theorem kuratowskiComplex_shift_continuous (F : IsometricFilling M) (x : M) :
    Continuous (fun θ : Circle2Pi => kuratowskiComplex F x (θ + (Real.pi : Circle2Pi))) :=
  (kuratowskiComplex_continuous F x).comp (continuous_id.add continuous_const)

/-- The antipodal difference profile is continuous on `Circle2Pi`. -/
theorem antipodalDiff_continuous (F : IsometricFilling M) (x : M) :
    Continuous (antipodalDiff F x) :=
  (kuratowskiComplex_continuous F x).sub (kuratowskiComplex_shift_continuous F x)

/-- The antipodal difference profile lies in `L²(haarAddCircle)`. -/
theorem antipodalDiff_memLp (F : IsometricFilling M) (x : M) :
    MemLp (antipodalDiff F x) 2 haarAddCircle :=
  (antipodalDiff_continuous F x).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- **Lemma 1 (Odd Fourier Mode Doubling):**
At every odd frequency `2 * k + 1`, `fourierCoeff (antipodalDiff F x) (2 * k + 1)`
equals `2 * fourierCoeff (kuratowskiComplex F x) (2 * k + 1)`. -/
theorem antipodalDiff_fourierCoeff_odd (F : IsometricFilling M) (x : M) (k : ℤ) :
    fourierCoeff (antipodalDiff F x) (2 * k + 1) =
      2 * fourierCoeff (kuratowskiComplex F x) (2 * k + 1) := by
  have hD : antipodalDiff F x = fun θ =>
      kuratowskiComplex F x θ - kuratowskiComplex F x (θ + (Real.pi : Circle2Pi)) := rfl
  rw [hD, fourierCoeff_sub_of_continuous _ _ (kuratowskiComplex_continuous F x)
    (kuratowskiComplex_shift_continuous F x), fourierCoeff_add_pi,
    (odd_two_mul_add_one k).neg_one_zpow]
  ring

/-- **Lemma 2 (Parseval Identity for `antipodalDiff`):**
The Haar `L²` norm squared of `antipodalDiff F x` equals the sum of squared
magnitudes of its Fourier coefficients. -/
theorem antipodalDiff_parseval_hasSum (F : IsometricFilling M) (x : M) :
    HasSum (fun n : ℤ => ‖fourierCoeff (antipodalDiff F x) n‖ ^ 2)
      (∫ θ : Circle2Pi, ‖antipodalDiff F x θ‖ ^ 2 ∂haarAddCircle) := by
  have hL := antipodalDiff_memLp F x
  convert hasSum_sq_fourierCoeff hL.toLp using 1
  · ext n
    rw [fourierCoeff_congr_ae hL.coeFn_toLp]
  · exact integral_congr_ae (hL.coeFn_toLp.mono fun t ht => by simp only [ht])

end

end

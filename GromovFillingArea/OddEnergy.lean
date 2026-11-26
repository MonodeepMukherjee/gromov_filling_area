/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.OddProjection

/-!
# Odd-Harmonic Spectral Energy Identity

This file splits the `ℤ`-indexed Parseval series of `antipodalDiff F x` into
even (`2 * k`) and odd (`2 * k + 1`) frequencies, proving that the even terms
vanish and `4 * ∑' k : ℤ, ‖f̂_x(2k+1)‖² = ∫ ‖Δ_x(θ)‖² ∂haarAddCircle`.
-/

open MeasureTheory Metric AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The odd-index map `k ↦ 2 * k + 1` on `ℤ` is injective. -/
theorem odd_index_injective : Function.Injective (fun k : ℤ => 2 * k + 1) := by
  intro a b h
  simp only at h
  omega

/-- The squared Fourier energies of `antipodalDiff F x` vanish off the odd indices. -/
theorem antipodalDiff_energy_eq_zero_of_not_odd (F : IsometricFilling M) (x : M) (n : ℤ)
    (hn : n ∉ Set.range (fun k : ℤ => 2 * k + 1)) :
    ‖fourierCoeff (antipodalDiff F x) n‖ ^ 2 = 0 := by
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [antipodalDiff_fourierCoeff_even, norm_zero]
    norm_num
  · exact absurd ⟨k, rfl⟩ hn

/-- **Lemma 1 (Summability of Odd Fourier Energies):**
The squared magnitudes of the odd Fourier coefficients `2 * k + 1` of
`kuratowskiComplex F x` are summable over `ℤ`. -/
theorem kuratowski_odd_fourier_summable (F : IsometricFilling M) (x : M) :
    Summable (fun k : ℤ => ‖fourierCoeff (kuratowskiComplex F x) (2 * k + 1)‖ ^ 2) :=
  (kuratowski_parseval_hasSum F x).summable.comp_injective odd_index_injective

/-- **Lemma 2 (Odd-Mode Parseval Energy Identity):**
Four times the sum of squared odd Fourier coefficients of `kuratowskiComplex F x`
equals the Haar `L²` norm squared of `antipodalDiff F x`. -/
theorem kuratowski_odd_fourier_energy_eq (F : IsometricFilling M) (x : M) :
    4 * (∑' k : ℤ, ‖fourierCoeff (kuratowskiComplex F x) (2 * k + 1)‖ ^ 2) =
      ∫ θ : Circle2Pi, ‖antipodalDiff F x θ‖ ^ 2 ∂haarAddCircle := by
  have h := (odd_index_injective.hasSum_iff
    (antipodalDiff_energy_eq_zero_of_not_odd F x)).mpr (antipodalDiff_parseval_hasSum F x)
  have h4 : HasSum (fun k : ℤ => 4 * ‖fourierCoeff (kuratowskiComplex F x) (2 * k + 1)‖ ^ 2)
      (∫ θ : Circle2Pi, ‖antipodalDiff F x θ‖ ^ 2 ∂haarAddCircle) := by
    convert h using 1
    funext k
    simp only [Function.comp_apply]
    rw [antipodalDiff_fourierCoeff_odd, norm_mul, Complex.norm_two]
    ring
  rw [← tsum_mul_left]
  exact h4.tsum_eq

end

end

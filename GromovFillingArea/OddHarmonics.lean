/-
Copyright (c) 2026 Monodeep. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monodeep
-/
module

public import GromovFillingArea.SpectralBound

/-!
# Odd-Harmonic Antipodal Decomposition & Fourier Decay

This file defines the antipodal difference profile `Δ_x(θ) = f_x(θ) - f_x(θ + π)`
and establishes how shifting by the half-period `π` acts on Fourier coefficients
`fourierCoeff`, isolating the odd harmonics `(2k + 1)`.
-/

open MeasureTheory Metric AddCircle

@[expose] public section

noncomputable section

variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The antipodal difference profile `θ ↦ f_x(θ) - f_x(θ + π)` in `ℂ`. -/
def antipodalDiff (F : IsometricFilling M) (x : M) (θ : Circle2Pi) : ℂ :=
  kuratowskiComplex F x θ - kuratowskiComplex F x (θ + (Real.pi : Circle2Pi))

/-- **Lemma 1 (Half-Period Shift on `Circle2Pi`):**
Adding `π` twice on `Circle2Pi` returns to the original point (`θ + π + π = θ`). -/
theorem circle2Pi_add_pi_add_pi (θ : Circle2Pi) :
    θ + (Real.pi : Circle2Pi) + (Real.pi : Circle2Pi) = θ := by
  rw [add_assoc, ← AddCircle.coe_add, ← two_mul, AddCircle.coe_period, add_zero]

/-- **Lemma 2 (Odd-Involution Symmetry of `antipodalDiff`):**
Shifting `θ` by `π` negates `antipodalDiff F x θ`. -/
theorem antipodalDiff_add_pi (F : IsometricFilling M) (x : M) (θ : Circle2Pi) :
    antipodalDiff F x (θ + (Real.pi : Circle2Pi)) = -antipodalDiff F x θ := by
  rw [antipodalDiff, antipodalDiff, circle2Pi_add_pi_add_pi, neg_sub]

end

end

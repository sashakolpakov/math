import Mathlib.RingTheory.DividedPowers.DPMorphism

/-! # Ideal Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.IdealTransport

/-! Divided-power compatibility is unchanged by a proved equality of
the target ideal. -/

variable {R A : Type*} [CommRing R] [CommRing A]
  {I : Ideal R} {J J' : Ideal A} (h : J = J')
  (δR : DividedPowers I) (δ : DividedPowers J) (f : R →+* A)

theorem isDPMorphism (hf : DividedPowers.IsDPMorphism δR δ f) :
    DividedPowers.IsDPMorphism δR (h ▸ δ) f := by
  cases h
  exact hf

end OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.IdealTransport

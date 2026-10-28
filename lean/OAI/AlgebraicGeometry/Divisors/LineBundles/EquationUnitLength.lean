import OAI.AlgebraicGeometry.Divisors.LineBundles.EquationEulerLength
import OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeIntersectionLength

/-! # Equation Unit Length -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.EquationUnitLength.BundleCycles

noncomputable section

/-!
# LineBundleCycles: multiplication by a unit has zero kernel and cokernel lengths
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem equationKernel_length_zero_of_unit (x : R) (hx : IsUnit x) :
    Module.length R (MultiplicationSequence.BundleCycles.equationKernel x M) = 0 := by
  obtain ⟨u, rfl⟩ := hx
  have hi : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism (u : R) M) :=
    (LinearEquiv.smulOfUnit (M := M) u).injective
  rw [MultiplicationSequence.BundleCycles.equationKernel, LinearMap.ker_eq_bot.mpr hi, Module.length_bot]

theorem equationCokernel_length_zero_of_unit (x : R) (hx : IsUnit x) :
    Module.length R (MultiplicationSequence.BundleCycles.equationCokernel x M) = 0 := by
  obtain ⟨u, rfl⟩ := hx
  have hs : Function.Surjective (MultiplicationSequence.BundleCycles.equationEndomorphism (u : R) M) :=
    (LinearEquiv.smulOfUnit (M := M) u).surjective
  change Module.length R (M ⧸ (MultiplicationSequence.BundleCycles.equationEndomorphism (u : R) M).range) = 0
  rw [LinearMap.range_eq_top.mpr hs]
  exact Module.length_eq_zero

theorem equationEulerLength_zero_of_unit (x : R) (hx : IsUnit x)
    (hK : Module.length R (MultiplicationSequence.BundleCycles.equationKernel x M) ≠ ⊤)
    (hC : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel x M) ≠ ⊤) :
    EquationEulerLength.BundleCycles.equationEulerLength x M hK hC = 0 := by
  unfold EquationEulerLength.BundleCycles.equationEulerLength
  rw [equationKernel_length_zero_of_unit x hx, equationCokernel_length_zero_of_unit x hx]
  rfl

theorem primeIntersectionQuotientLength_unit (x : R) (hx : IsUnit x) (P : Ideal R) :
    PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength x P = 0 := by
  unfold PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength
  rw [Ideal.span_singleton_eq_top.mpr hx, sup_top_eq, Module.length_eq_zero]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.EquationUnitLength.BundleCycles

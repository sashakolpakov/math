import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Powers
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IdealQuotient

/-! # Basis -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Basis.FreeDividedBasis

noncomputable section

/-!
# Divided-monomial coefficients over arbitrary rings

Linear coefficient functionals on a characteristic-zero presentation
preserve every ideal extended from its coefficient ring. The actual
coefficient-quotient equivalence therefore proves independence of divided
monomials over arbitrary commutative rings, including rings with torsion.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

section Quotient

variable (S R σ K : Type u) [CommRing S] [CommRing R] [Algebra S R]
  [Field K] [CharZero K] [Algebra S K]
  (h : Function.Injective (algebraMap S K))
  (hs : Function.Surjective (algebraMap S R))

local notation "GS" => DividedPowerAlgebra S (σ →₀ S)
local notation "L" => RingHom.ker (algebraMap S R)

include h hs in
theorem fromCoefficients_eq_zero {v : (σ →₀ ℕ) →₀ R}
    (hv : Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients R σ v = 0) : v = 0 := by
  obtain ⟨w, rfl⟩ := Finsupp.mapRange_surjective (algebraMap S R) (map_zero _) hs v
  have hm : Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map S R σ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients S σ w) = 0 := by
    rw [Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map_fromCoefficients, hv]
  have hq : Divided.AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.quotient S R σ hs
      (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients S σ w) = 0 := by
    apply (Divided.AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.algebraEquiv S R σ K h hs).symm.injective
    change Divided.AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.toTarget S R σ hs
      (Divided.AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.quotient S R σ hs (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients S σ w)) = _
    rw [Divided.AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.toTarget_quotient, hm, map_zero]
  have hw : Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients S σ w ∈ (L).map (algebraMap S GS) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hq
  ext d
  change algebraMap S R (w d) = 0
  let f : GS →ₗ[S] S := (Finsupp.lapply d).comp (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.coefficientEquiv S σ K h).symm.toLinearMap
  have hf : f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients S σ w) = w d := by
    change ((Multivariable.DividedAlgebra.MultivariableDividedAlgebra.coefficientEquiv S σ K h).symm ((Multivariable.DividedAlgebra.MultivariableDividedAlgebra.coefficientEquiv S σ K h) w)) d = w d
    rw [LinearEquiv.symm_apply_apply]
  have hc := Base.IdealQuotient.BaseIdealQuotient.map_mem L f hw
  rw [hf, Algebra.algebraMap_self, Ideal.map_id] at hc
  exact hc

include h hs in
theorem fromCoefficients_injective_of_quotient : Function.Injective (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients R σ) := by
  intro v w hvw
  apply sub_eq_zero.mp
  apply fromCoefficients_eq_zero S R σ K h hs
  rw [map_sub, hvw, sub_self]

end Quotient

variable (R σ : Type u) [CommRing R]

/-- Independence of actual divided monomials without any characteristic hypothesis. -/
theorem fromCoefficients_injective : Function.Injective (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients R σ) :=
  fromCoefficients_injective_of_quotient (Powers.FreeDividedPowers.Source R) R σ
    (FractionRing (Powers.FreeDividedPowers.Source R)) (Powers.FreeDividedPowers.fraction_injective R)
    (Powers.FreeDividedPowers.reduction_surjective R)

/-- Every actual free divided-power element has unique finitely supported coefficients. -/
def coefficientEquiv : ((σ →₀ ℕ) →₀ R) ≃ₗ[R] DividedPowerAlgebra R (σ →₀ R) :=
  LinearEquiv.ofBijective (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients R σ)
    ⟨fromCoefficients_injective R σ, Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients_surjective R σ⟩

theorem coefficients_monomial (d : σ →₀ ℕ) :
    (coefficientEquiv R σ).symm (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d) = Finsupp.single d 1 := by
  apply (coefficientEquiv R σ).injective
  rw [LinearEquiv.apply_symm_apply]
  exact ((Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients_single R σ d 1).trans (one_smul R _)).symm

def basis : Module.Basis (σ →₀ ℕ) R (DividedPowerAlgebra R (σ →₀ R)) :=
  Finsupp.basisSingleOne.map (coefficientEquiv R σ)

theorem basis_apply (d : σ →₀ ℕ) : basis R σ d = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d := by
  change Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients R σ (Finsupp.single d 1) = _
  rw [Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients_single, one_smul]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Basis.FreeDividedBasis

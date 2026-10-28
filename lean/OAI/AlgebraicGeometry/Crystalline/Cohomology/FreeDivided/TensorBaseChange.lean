import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Localization.BaseChange

/-! # Tensor Base Change -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.TensorBaseChange.FreeDividedTensorBaseChange

noncomputable section

/-!
# Tensor base change and localization of actual free divided-power algebras

Extending the coefficients of the actual free divided-power algebra agrees
with algebraic tensor base change. The proof uses its proved divided-monomial
basis over arbitrary rings. In particular coefficient localizations produce
the corresponding localizations of the actual divided-power algebra.
-/

open scoped TensorProduct

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R S σ : Type u) [CommRing R] [CommRing S] [Algebra R S]

local notation "GR" => DividedPowerAlgebra R (σ →₀ R)
local notation "GS" => DividedPowerAlgebra S (σ →₀ S)

def tensorMap : (S ⊗[R] GR) →ₐ[S] GS :=
  AlgHom.liftEquiv R S GR GS (Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map R S σ)

theorem tensorMap_tmul (s : S) (a : GR) :
    tensorMap R S σ (s ⊗ₜ[R] a) = s • Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map R S σ a := rfl

def basisEquiv : (S ⊗[R] GR) ≃ₗ[S] GS :=
  ((FreeDivided.Basis.FreeDividedBasis.basis R σ).baseChange S).equiv (FreeDivided.Basis.FreeDividedBasis.basis S σ) (Equiv.refl _)

theorem tensorMap_eq_basisEquiv : (tensorMap R S σ).toLinearMap = (basisEquiv R S σ).toLinearMap := by
  apply ((FreeDivided.Basis.FreeDividedBasis.basis R σ).baseChange S).ext
  intro d
  have he := ((FreeDivided.Basis.FreeDividedBasis.basis R σ).baseChange S).equiv_apply d
    (FreeDivided.Basis.FreeDividedBasis.basis S σ) (Equiv.refl _)
  change tensorMap R S σ (((FreeDivided.Basis.FreeDividedBasis.basis R σ).baseChange S) d) = basisEquiv R S σ _
  rw [show basisEquiv R S σ (((FreeDivided.Basis.FreeDividedBasis.basis R σ).baseChange S) d) =
    FreeDivided.Basis.FreeDividedBasis.basis S σ d from he,
    Module.Basis.baseChange_apply, FreeDivided.Basis.FreeDividedBasis.basis_apply, tensorMap_tmul,
    Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map_monomial, one_smul, FreeDivided.Basis.FreeDividedBasis.basis_apply]

def algebraEquiv : (S ⊗[R] GR) ≃ₐ[S] GS :=
  AlgEquiv.ofBijective (tensorMap R S σ) (by
    change Function.Bijective (tensorMap R S σ).toLinearMap
    rw [tensorMap_eq_basisEquiv]
    exact (basisEquiv R S σ).bijective)

theorem algebraEquiv_tmul (s : S) (a : GR) :
    algebraEquiv R S σ (s ⊗ₜ[R] a) = s • Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map R S σ a :=
  tensorMap_tmul R S σ s a

instance coefficientAlgebra : Algebra GR GS :=
  (Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map R S σ).toRingHom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Tensor base change also respects the original divided-power coefficient algebra. -/
def rightEquiv : (S ⊗[R] GR) ≃ₐ[GR] GS where
  __ := (algebraEquiv R S σ).toRingEquiv
  commutes' a := by
    change algebraEquiv R S σ (1 ⊗ₜ[R] a) = Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map R S σ a
    rw [algebraEquiv_tmul, one_smul]

theorem isLocalization (M : Submonoid R) [IsLocalization M S] :
    IsLocalization (Algebra.algebraMapSubmonoid GR M) GS :=
  IsLocalization.isLocalization_of_algEquiv (S := S ⊗[R] GR) _ (rightEquiv R S σ)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.TensorBaseChange.FreeDividedTensorBaseChange

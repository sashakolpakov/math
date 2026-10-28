import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.LiftDerivations
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Lift Finiteness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.LiftFiniteness.RelativeLifts

noncomputable section

/-! Relative lifts of an essentially finite-type algebra form a finite
module over a noetherian coefficient ring, via the actual cotangent module. -/

open scoped TensorProduct

variable (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra B C] [Algebra R C] [IsScalarTower R B C]
  (J : Ideal C)

def coefficientDerivationEquiv :
    Derivation R B J ≃ₗ[C] (KaehlerDifferential R B →ₗ[B] J) where
  toEquiv := (KaehlerDifferential.linearMapEquivDerivation R B).symm.toEquiv
  map_add' := (KaehlerDifferential.linearMapEquivDerivation R B).symm.map_add
  map_smul' c d := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro b
    change (c • d).liftKaehlerDifferential (KaehlerDifferential.D R B b) =
      c • d.liftKaehlerDifferential (KaehlerDifferential.D R B b)
    rw [Derivation.liftKaehlerDifferential_comp_D, Derivation.liftKaehlerDifferential_comp_D]
    rfl

def cotangentEquiv : Derivation R B J ≃ₗ[C]
    (C ⊗[B] KaehlerDifferential R B →ₗ[C] J) :=
  (coefficientDerivationEquiv R B C J).trans (LinearMap.liftBaseChangeEquiv C)

theorem finite [IsNoetherianRing C] [Algebra.EssFiniteType R B] (hJ : J ^ 2 = ⊥) :
    Module.Finite C (LiftDerivations.RelativeLifts.module R B C J hJ) := by
  let : Module.Finite C (C ⊗[B] KaehlerDifferential R B) := inferInstance
  let : IsNoetherian C J := inferInstance
  let : Module.Finite C (Derivation R B J) :=
    Module.Finite.equiv (cotangentEquiv R B C J).symm
  exact Module.Finite.of_injective (LiftDerivations.RelativeLifts.derivation R B C J hJ) (LiftDerivations.RelativeLifts.derivation_injective R B C J hJ)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.LiftFiniteness.RelativeLifts

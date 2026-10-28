import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.BasisLocalDualRelations

/-! # Coefficient Dual Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientDualAction

noncomputable section

/-! Coefficient-dual action data is transported through an equality of
coefficient algebra structures before specializing to geometric modules. -/

variable {O R V I : Type} [CommRing O] [CommRing R] [AddCommGroup V] [Module R V]
  (b : Module.Basis I ℤ O) (d : I → Module.End R V)

def CoefficientDualActionExists (C : Type) [CommRing C] (α : Algebra R C) : Prop :=
  letI := α
  letI : Module R C := Algebra.toModule
  ∃ τ : O →+* Module.End C (V →ₗ[R] C),
    ∀ i (ℓ : V →ₗ[R] C) v, ℓ (d i v) = (τ (b i) ℓ) v

theorem coefficientDualActionExists_transport {C : Type} [CommRing C]
    {α β : Algebra R C} (h : α = β) :
    CoefficientDualActionExists b d C α → CoefficientDualActionExists b d C β := by
  cases h
  exact id

theorem integralBasisActionRelations_of_coefficientDualActions [Module.IsReflexive R V]
    (h : ∀ (P : Ideal R) (_ : P.IsMaximal),
      CoefficientDualActionExists b d (Localization.AtPrime P) inferInstance) :
    Integral.BasisActionRelations.IntegralBasisActionRelations b d := by
  apply Integral.BasisLocalDualRelations.integralBasisActionRelations_of_localDualActions b d
  intro P hP
  exact h P hP

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientDualAction

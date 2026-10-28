import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CharacterQuotient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ActionExtension
import Mathlib.RingTheory.Etale.Field
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Character Quotient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.CharacterQuotient

noncomputable section

/-! Extend an actual integral number-field representation on a
projective module over a rational algebra. Its original finite integral
character quotient is projective, via the constructed unramified splitting. -/

open scoped TensorProduct

variable {E R V I : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module ℚ V] [IsScalarTower ℚ R V]

def integralCharacterTensorAction
    (ρ : NumberField.RingOfIntegers E →+* Module.End R V) :
    R ⊗[ℚ] E →ₐ[R] Module.End R V :=
  Algebra.TensorProduct.lift (Algebra.ofId R (Module.End R V)) (ActionExtension.extendIntegralAction ρ)
    (fun r x => Algebra.commutes r (ActionExtension.extendIntegralAction ρ x))

theorem integralCharacterTensorAction_integer
    (ρ : NumberField.RingOfIntegers E →+* Module.End R V)
    (a : NumberField.RingOfIntegers E) :
    integralCharacterTensorAction ρ (1 ⊗ₜ[ℚ] (a : E)) = ρ a := by
  change algebraMap R (Module.End R V) 1 * ActionExtension.extendIntegralAction ρ (a : E) = ρ a
  rw [map_one, one_mul, ActionExtension.extendIntegralAction_integer]

def integralCharacterTensorMap (χ : NumberField.RingOfIntegers E →+* R) :
    R ⊗[ℚ] E →ₐ[R] R :=
  Algebra.TensorProduct.lift (AlgHom.id R R) (ActionExtension.extendIntegralAction χ)
    (fun r x => Commute.all r (ActionExtension.extendIntegralAction χ x))

omit [Module R V] [Module ℚ V] [IsScalarTower ℚ R V] in
theorem integralCharacterTensorMap_integer (χ : NumberField.RingOfIntegers E →+* R)
    (a : NumberField.RingOfIntegers E) :
    integralCharacterTensorMap χ (1 ⊗ₜ[ℚ] (a : E)) = χ a := by
  change 1 * ActionExtension.extendIntegralAction χ (a : E) = χ a
  rw [one_mul, ActionExtension.extendIntegralAction_integer]

def integralCharacterTensorBasis (b : Module.Basis I ℤ (NumberField.RingOfIntegers E)) :
    Module.Basis I R (R ⊗[ℚ] E) :=
  (b.localizationLocalization ℚ (nonZeroDivisors ℤ) E).baseChange R

omit [Module R V] [Module ℚ V] [IsScalarTower ℚ R V] in
theorem integralCharacterTensorBasis_apply
    (b : Module.Basis I ℤ (NumberField.RingOfIntegers E)) (i : I) :
    integralCharacterTensorBasis (R := R) b i = 1 ⊗ₜ[ℚ] (b i : E) := by
  rw [integralCharacterTensorBasis, Module.Basis.baseChange_apply,
    Module.Basis.localizationLocalization_apply]

theorem integralCharacterQuotient_projective
    [Fintype I] [Module.Projective R V]
    (b : Module.Basis I ℤ (NumberField.RingOfIntegers E))
    (ρ : NumberField.RingOfIntegers E →+* Module.End R V)
    (χ : NumberField.RingOfIntegers E →+* R) :
    Module.Projective R (PELModuli.IntegralModel.ConormalEigenquotient.conormalEigenquotient (fun i => ρ (b i)) (fun i => χ (b i))) := by
  let : Algebra.FormallyEtale ℚ E := Algebra.FormallyEtale.of_isSeparable ℚ E
  let a := integralCharacterTensorAction ρ
  let : Module (R ⊗[ℚ] E) V := Module.compHom V a.toRingHom
  let : IsScalarTower R (R ⊗[ℚ] E) V := ⟨fun r x v => by
    change a (r • x) v = r • a x v
    exact LinearMap.congr_fun (a.toLinearMap.map_smul r x) v⟩
  have hd : (fun i => (Algebra.lsmul R R V) (integralCharacterTensorBasis (R := R) b i)) =
      (fun i => ρ (b i)) := by
    funext i
    change a (integralCharacterTensorBasis (R := R) b i) = ρ (b i)
    rw [integralCharacterTensorBasis_apply]
    exact integralCharacterTensorAction_integer ρ (b i)
  have hχ : (fun i => integralCharacterTensorMap χ (integralCharacterTensorBasis (R := R) b i)) =
      (fun i => χ (b i)) := by
    funext i
    rw [integralCharacterTensorBasis_apply, integralCharacterTensorMap_integer]
  have h := ReferenceFamily.Finite.CharacterQuotient.finiteCharacterQuotient_projective (V := V)
    (integralCharacterTensorBasis (R := R) b) (integralCharacterTensorMap χ)
  rw [hd, hχ] at h
  exact h

theorem integralCharacterQuotient_rank_isLocallyConstant
    [Fintype I] [Module.Projective R V] [Module.Finite R V] [IsNoetherianRing R]
    (b : Module.Basis I ℤ (NumberField.RingOfIntegers E))
    (ρ : NumberField.RingOfIntegers E →+* Module.End R V)
    (χ : NumberField.RingOfIntegers E →+* R) :
    IsLocallyConstant (Module.rankAtStalk (R := R)
      (PELModuli.IntegralModel.ConormalEigenquotient.conormalEigenquotient (fun i => ρ (b i)) (fun i => χ (b i)))) := by
  let : Module.Projective R (PELModuli.IntegralModel.ConormalEigenquotient.conormalEigenquotient (fun i => ρ (b i)) (fun i => χ (b i))) :=
    integralCharacterQuotient_projective b ρ χ
  let : Module.FinitePresentation R (PELModuli.IntegralModel.ConormalEigenquotient.conormalEigenquotient (fun i => ρ (b i)) (fun i => χ (b i))) :=
    PELModuli.IntegralModel.ConormalEigenquotient.conormalEigenquotient_finitePresentation _ _
  exact Module.isLocallyConstant_rankAtStalk

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.CharacterQuotient

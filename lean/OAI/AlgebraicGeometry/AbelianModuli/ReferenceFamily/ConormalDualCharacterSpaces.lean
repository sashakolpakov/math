import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.JointCharacterDecomposition
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalLieRanks
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.RosatiExtension

/-! # Conormal Dual Character Spaces -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The joint character spaces of the actual dual conormal action
are the spaces whose dimensions are given by the original Lie ranks.
Distinct number-field embeddings remain distinct on the integers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem ConormalDualCharacterSpaces.integerEmbeddingRestriction_injective
    {E k : Type*} [Field E] [NumberField E] [Algebra ℚ E]
    [Field k] [Algebra ℚ k] :
    Function.Injective (fun σ : E →ₐ[ℚ] k => fun a : NumberField.RingOfIntegers E => σ (a : E)) := by
  intro σ τ h
  have he : σ.toLinearMap = τ.toLinearMap :=
    Integral.RosatiExtension.rationalLinearMap_eq_of_integers σ.toLinearMap τ.toLinearMap (fun a => congrFun h a)
  exact AlgHom.ext (fun x => LinearMap.congr_fun he x)

variable {O : Type} [CommRing O] {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction O A)

local instance ConormalDualCharacterSpaces.characterConormalIntegral : IsIntegral A.scheme.left := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral A

def ConormalDualCharacterSpaces.constructedConormalDualOperator (a : O) :
    Module.End ℂ (Constructed.IdentityConormal.constructedIdentityConormal ℂ A.scheme →ₗ[ℂ] ℂ) :=
  (Constructed.ConormalIntegralAction.constructedConormalIntegralAction A ρ a).dualMap

theorem ConormalDualCharacterSpaces.jointCharacterSpace_conormalDual (τ : O →+* ℂ) :
    JointCharacterDecomposition.jointCharacterSpace (ConormalDualCharacterSpaces.constructedConormalDualOperator A ρ) τ =
      Constructed.ConormalLieRanks.constructedConormalDualEigenSpace A ρ τ := by
  ext l
  constructor
  · intro h a z
    exact LinearMap.congr_fun (h a) z
  · intro h a
    exact LinearMap.ext (h a)

theorem LieRanks.HasLieRank.jointConormalCharacter_finrank (τ : O →+* ℂ) {r : ℕ}
    (hr : LieRanks.HasLieRank A ρ τ r) :
    Module.finrank ℂ (JointCharacterDecomposition.jointCharacterSpace (ConormalDualCharacterSpaces.constructedConormalDualOperator A ρ) τ) = r := by
  rw [ConormalDualCharacterSpaces.jointCharacterSpace_conormalDual]
  exact hr.constructedConormalDual_finrank A ρ τ

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

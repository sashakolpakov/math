import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConormalDualCharacterSpaces
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.JointCharacterBasis
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PrimalCharacterBasis
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.LieRanks

/-! # Conormal Character Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis

noncomputable section

/-! The native tangent/conormal comparison and the original PEL Lie
ranks construct character bases of the actual conormal and its dual. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s)

def pairedIntegralCharacter (j : Fin s × Bool) : NumberField.RingOfIntegers E →+* ℂ :=
  (P.pairedEmbedding j).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)

theorem pairedIntegralCharacter_injective (hP : P.IsAdmissible) :
    Function.Injective (fun j => (pairedIntegralCharacter P j : NumberField.RingOfIntegers E → ℂ)) :=
  (ConormalDualCharacterSpaces.integerEmbeddingRestriction_injective (E := E) (k := ℂ)).comp
    (P.pairedEmbedding_injective hP)

variable (A : HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

local instance pelBasisConormal_integral : IsIntegral A.scheme.left := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral A

theorem constructedConormalDual_finrank :
    Module.finrank ℂ (Constructed.IdentityConormal.constructedIdentityConormal ℂ A.scheme →ₗ[ℂ] ℂ) = 3 * s :=
  (Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A.scheme).finrank_eq.symm.trans
    ((Module.finrank_fin_fun ℂ).trans (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.dimension_eq A))

variable (hP : P.IsAdmissible)
    (hr : ∀ j, LieRanks.HasLieRank A ρ (pairedIntegralCharacter P j) (P.pairedLieRank j))

def pelConormalDualCharacterBasis :
    Module.Basis (Σ j, Fin (P.pairedLieRank j)) ℂ
      (Constructed.IdentityConormal.constructedIdentityConormal ℂ A.scheme →ₗ[ℂ] ℂ) :=
  JointCharacterBasis.jointCharacterBasisOfRanks (ConormalDualCharacterSpaces.constructedConormalDualOperator A ρ)
    (fun j => pairedIntegralCharacter P j) (pairedIntegralCharacter_injective P hP)
    P.pairedLieRank (fun j => (hr j).jointConormalCharacter_finrank A ρ _)
    (P.pairedLieRank_sum.trans (constructedConormalDual_finrank A).symm)

theorem pelConormalDualCharacterBasis_eigen (j : Σ j, Fin (P.pairedLieRank j))
    (a : NumberField.RingOfIntegers E) :
    (Constructed.ConormalIntegralAction.constructedConormalIntegralAction A ρ a).dualMap
        (pelConormalDualCharacterBasis P A ρ hP hr j) =
      pairedIntegralCharacter P j.1 a • pelConormalDualCharacterBasis P A ρ hP hr j :=
  JointCharacterBasis.jointCharacterBasisOfRanks_eigen (ConormalDualCharacterSpaces.constructedConormalDualOperator A ρ)
    (fun j => pairedIntegralCharacter P j) (pairedIntegralCharacter_injective P hP)
    P.pairedLieRank (fun j => (hr j).jointConormalCharacter_finrank A ρ _)
    (P.pairedLieRank_sum.trans (constructedConormalDual_finrank A).symm) j a

def pelConormalCharacterBasis :
    Module.Basis (Σ j, Fin (P.pairedLieRank j)) ℂ (Constructed.IdentityConormal.constructedIdentityConormal ℂ A.scheme) :=
  PrimalCharacterBasis.primalBasisOfDualBasis (pelConormalDualCharacterBasis P A ρ hP hr)

theorem pelConormalCharacterBasis_eigen (j : Σ j, Fin (P.pairedLieRank j))
    (a : NumberField.RingOfIntegers E) :
    Constructed.ConormalIntegralAction.constructedConormalIntegralAction A ρ a (pelConormalCharacterBasis P A ρ hP hr j) =
      pairedIntegralCharacter P j.1 a • pelConormalCharacterBasis P A ρ hP hr j :=
  PrimalCharacterBasis.primalBasisOfDualBasis_eigen (pelConormalDualCharacterBasis P A ρ hP hr)
    (Constructed.ConormalIntegralAction.constructedConormalIntegralAction A ρ) (fun j => pairedIntegralCharacter P j.1)
    (pelConormalDualCharacterBasis_eigen P A ρ hP hr) j a

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis

import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELCharacterSupportIndices
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BalancedBilinearEigenvectors

/-! # PEL Character Conjugation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELCharacterConjugation.Construction

noncomputable section

/-! Conjugation of the original integral character switches its actual
CM embedding label. Balanced forms on the constructed character basis
therefore have support only on the distinguished two-by-one pair. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BalancedBilinearEigenvectors

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

theorem pairedIntegralCharacter_conjugation (j : Fin s × Bool) :
    (fun a => AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis.pairedIntegralCharacter P j (NumberField.IsCMField.ringOfIntegersComplexConj E a)) =
      (AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis.pairedIntegralCharacter P (j.1, !j.2) : NumberField.RingOfIntegers E → ℂ) := by
  funext a
  change (P.pairedEmbedding j) ((NumberField.IsCMField.ringOfIntegersComplexConj E a :
    NumberField.RingOfIntegers E) : E) = (P.pairedEmbedding (j.1, !j.2)) (a : E)
  rw [NumberField.IsCMField.coe_ringOfIntegersComplexConj]
  change (P.pairedEmbedding j).toRingHom ((NumberField.IsCMField.complexConj E) (a : E)) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj E (P.pairedEmbedding j).toRingHom]
  rcases j with ⟨i, b⟩
  cases b <;> simp [AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.pairedEmbedding, ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_apply]

theorem pairedIntegralCharacter_conjugate_eq_iff (hP : P.IsAdmissible) (i j : Fin s × Bool) :
    (AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis.pairedIntegralCharacter P i : NumberField.RingOfIntegers E → ℂ) =
      (AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis.pairedIntegralCharacter P j : NumberField.RingOfIntegers E → ℂ) ∘
        NumberField.IsCMField.ringOfIntegersComplexConj E ↔ i = (j.1, !j.2) := by
  change (AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis.pairedIntegralCharacter P i : NumberField.RingOfIntegers E → ℂ) =
    (fun a => AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis.pairedIntegralCharacter P j (NumberField.IsCMField.ringOfIntegersComplexConj E a)) ↔ _
  rw [pairedIntegralCharacter_conjugation]
  exact (AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis.pairedIntegralCharacter_injective P hP).eq_iff

variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (hP : P.IsAdmissible)
    (hr : ∀ j, AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ (AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis.pairedIntegralCharacter P j) (P.pairedLieRank j))

local instance characterSupportIntegral : IsIntegral A.scheme.left :=
  AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral A

theorem pelBalancedBilinear_characterSupport
    (B : AbelianModuli.ReferenceFamily.Constructed.IdentityConormal.constructedIdentityConormal ℂ A.scheme →ₗ[ℂ]
      AbelianModuli.ReferenceFamily.Constructed.IdentityConormal.constructedIdentityConormal ℂ A.scheme →ₗ[ℂ] ℂ)
    (hB : ∀ a z w, B (AbelianModuli.ReferenceFamily.Constructed.ConormalIntegralAction.constructedConormalIntegralAction A ρ a z) w =
      B z (AbelianModuli.ReferenceFamily.Constructed.ConormalIntegralAction.constructedConormalIntegralAction A ρ
        (NumberField.IsCMField.ringOfIntegersComplexConj E a) w))
    (i j : PELCharacterSupportIndices.Construction.pelConormalBasisIndex P)
    (hn : ¬ ((i ∈ PELCharacterSupportIndices.Construction.pelPositiveTangentIndices P ∧ j ∈ PELCharacterSupportIndices.Construction.pelNegativeTangentIndices P) ∨
      (i ∈ PELCharacterSupportIndices.Construction.pelNegativeTangentIndices P ∧ j ∈ PELCharacterSupportIndices.Construction.pelPositiveTangentIndices P))) :
    B (AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis.pelConormalCharacterBasis P A ρ hP hr i)
      (AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis.pelConormalCharacterBasis P A ρ hP hr j) = 0 := by
  apply AbelianModuli.ReferenceFamily.BalancedBilinearEigenvectors.balancedBilinear_basis_zero (AbelianModuli.ReferenceFamily.Constructed.ConormalIntegralAction.constructedConormalIntegralAction A ρ)
    (NumberField.IsCMField.ringOfIntegersComplexConj E) B hB
    (AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis.pelConormalCharacterBasis P A ρ hP hr)
    (fun k => AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis.pairedIntegralCharacter P k.1)
    (AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis.pelConormalCharacterBasis_eigen P A ρ hP hr) i j
  intro he
  exact hn (PELCharacterSupportIndices.Construction.pelConjugateIndices_distinguished P i j
    ((pairedIntegralCharacter_conjugate_eq_iff P hP i.1 j.1).mp he))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELCharacterConjugation.Construction

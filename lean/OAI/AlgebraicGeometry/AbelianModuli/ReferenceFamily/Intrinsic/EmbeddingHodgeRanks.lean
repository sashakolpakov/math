import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingHodgeCriterion
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingPeriodProjection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking

/-! # Embedding Hodge Ranks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingHodgeRanks.IntrinsicNumberFieldAction

noncomputable section

/-! The actual rank-three period marking and original Lie-rank
condition determine both Hodge dimensions at every embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

def holomorphicEmbeddingPart (σ : E →ₐ[ℚ] ℂ) :
    Submodule ℂ (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).ker :=
  (EmbeddingPeriodProjection.IntrinsicNumberFieldAction.nativeEmbeddingSpace A P ρ σ).comap (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).ker.subtype

theorem nativeEmbedding_hodge_rank_sum (s : ℕ) (hs : 0 < s)
    (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s) (σ : E →ₐ[ℚ] ℂ) :
    Module.finrank ℂ (holomorphicEmbeddingPart A P ρ σ) +
      Module.finrank ℂ (EmbeddingPeriodProjection.IntrinsicNumberFieldAction.conjugateEmbeddingPart A P ρ σ) = 3 := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A P ρ
  have hact (a : E) : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P))
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P))
      (ComplexMultiplication.WeightOne.CM.scalarEndomorphism (U := RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) E a) :=
    Complex.PeriodFieldAction.IntrinsicNumberFieldAction.fieldAction_isHodgeMap A P ρ a
  have h := EmbeddingHodgeCriterion.embeddingSpace_hodge_finrank (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) hact σ
  have hdim := RankThreeEmbeddingCoordinates.rankThreeEmbeddingSpace_finrank E (PELMarking.IntrinsicPELMarking.coordinates A P ρ s hs hg hdegree) σ
  exact h.trans hdim

theorem holomorphicEmbeddingPart_finrank (s : ℕ) (hs : 0 < s)
    (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (σ : E →ₐ[ℚ] ℂ) {r : ℕ}
    (hr : LieRanks.HasLieRank A ρ (σ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) r) :
    Module.finrank ℂ (holomorphicEmbeddingPart A P ρ σ) = 3 - r := by
  have h := nativeEmbedding_hodge_rank_sum A P ρ s hs hg hdegree σ
  have hq := EmbeddingPeriodProjection.IntrinsicNumberFieldAction.conjugateEmbeddingPart_finrank A P ρ σ hr
  omega

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingHodgeRanks.IntrinsicNumberFieldAction

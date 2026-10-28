import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.FieldEigenspaces
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodComplementProjection

/-! # Embedding Period Projection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingPeriodProjection.IntrinsicNumberFieldAction

noncomputable section

/-! On each number-field embedding, the complementary period subspace
maps isomorphically to the actual native tangent eigenspace. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodComplementProjection.IntrinsicRationalPeriods

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

def nativeEmbeddingSpace (σ : E →ₐ[ℚ] ℂ) : Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P))) := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A P ρ
  exact ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) σ

def conjugateEmbeddingPart (σ : E →ₐ[ℚ] ℂ) : Submodule ℂ (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.conjugatePeriodKernel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) :=
  (nativeEmbeddingSpace A P ρ σ).comap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.conjugatePeriodKernel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).subtype

def embeddingPeriodProjection (σ : E →ₐ[ℚ] ℂ) :
    conjugateEmbeddingPart A P ρ σ →ₗ[ℂ] Complex.FieldEigenspaces.IntrinsicNumberFieldAction.complexFieldEigenspace A P ρ σ := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A P ρ
  exact ((PeriodComplementProjection.IntrinsicRationalPeriods.conjugatePeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).domRestrict (conjugateEmbeddingPart A P ρ σ)).codRestrict
    (Complex.FieldEigenspaces.IntrinsicNumberFieldAction.complexFieldEigenspace A P ρ σ) (fun u a => by
      have hu := (ComplexMultiplication.EmbeddingDecomposition.CM.mem_embeddingSpace E (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) σ u.val.val).mp u.property a
      have hf : (Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction A P ρ a).baseChange ℂ u.val.val = σ a • u.val.val := hu
      exact (Complex.PeriodFieldAction.IntrinsicNumberFieldAction.complexPeriodProjection_fieldAction A P ρ a u.val.val).symm.trans
        ((congrArg (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) hf).trans
          ((Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).map_smul (σ a) u.val.val)))

theorem embeddingPeriodProjection_bijective (σ : E →ₐ[ℚ] ℂ) :
    Function.Bijective (embeddingPeriodProjection A P ρ σ) := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A P ρ
  constructor
  · intro u v h
    apply Subtype.ext
    apply (PeriodComplementProjection.IntrinsicRationalPeriods.conjugatePeriodProjectionEquiv (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).injective
    exact congrArg (fun w : Complex.FieldEigenspaces.IntrinsicNumberFieldAction.complexFieldEigenspace A P ρ σ => w.val) h
  · intro v
    let q := (PeriodComplementProjection.IntrinsicRationalPeriods.conjugatePeriodProjectionEquiv (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).symm v.val
    have hq : Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) q.val = v.val :=
      (PeriodComplementProjection.IntrinsicRationalPeriods.conjugatePeriodProjectionEquiv (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).apply_symm_apply v.val
    have heigen : q.val ∈ ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) σ := by
      apply (ComplexMultiplication.EmbeddingDecomposition.CM.mem_embeddingSpace E (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) σ q.val).mpr
      intro a
      have hfa : (Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction A P ρ a).baseChange ℂ q.val ∈ IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.conjugatePeriodKernel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) :=
        (Complex.PeriodFieldAction.IntrinsicNumberFieldAction.fieldAction_isHodgeMap A P ρ a).map_antiholomorphic q.property
      have hsa : σ a • q.val ∈ IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.conjugatePeriodKernel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) :=
        (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.conjugatePeriodKernel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).smul_mem (σ a) q.property
      have hh : (⟨(Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction A P ρ a).baseChange ℂ q.val, hfa⟩ : IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.conjugatePeriodKernel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) =
          ⟨σ a • q.val, hsa⟩ := by
        apply (PeriodComplementProjection.IntrinsicRationalPeriods.conjugatePeriodProjectionEquiv (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).injective
        change Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) ((Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction A P ρ a).baseChange ℂ q.val) =
          Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) (σ a • q.val)
        exact (Complex.PeriodFieldAction.IntrinsicNumberFieldAction.complexPeriodProjection_fieldAction A P ρ a q.val).trans
          ((congrArg (Complex.PeriodFieldAction.IntrinsicNumberFieldAction.complexFieldAction A P ρ a) hq).trans
            ((v.property a).trans ((congrArg (fun w => σ a • w) hq).symm.trans
              ((Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).map_smul (σ a) q.val).symm)))
      exact congrArg Subtype.val hh
    refine ⟨⟨q, heigen⟩, ?_⟩
    exact Subtype.ext hq

def embeddingPeriodProjectionEquiv (σ : E →ₐ[ℚ] ℂ) :
    conjugateEmbeddingPart A P ρ σ ≃ₗ[ℂ] Complex.FieldEigenspaces.IntrinsicNumberFieldAction.complexFieldEigenspace A P ρ σ :=
  LinearEquiv.ofBijective (embeddingPeriodProjection A P ρ σ) (embeddingPeriodProjection_bijective A P ρ σ)

theorem conjugateEmbeddingPart_finrank (σ : E →ₐ[ℚ] ℂ) {r : ℕ}
    (hr : LieRanks.HasLieRank A ρ (σ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) r) :
    Module.finrank ℂ (conjugateEmbeddingPart A P ρ σ) = r :=
  (embeddingPeriodProjectionEquiv A P ρ σ).finrank_eq.trans (Complex.FieldEigenspaces.IntrinsicNumberFieldAction.complexFieldEigenspace_finrank A P ρ σ hr)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingPeriodProjection.IntrinsicNumberFieldAction

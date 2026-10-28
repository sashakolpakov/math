import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Polynomial
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AbsorbedOperators
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SpecializedPolynomialPredicate

/-! # Specialized Polynomial -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SpecializedPolynomial

noncomputable section

/-! Specialize the absorbed polynomial before substituting a constructed
Hecke model, so the comparison model remains abstract during the check. -/

open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct
open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic

attribute [local instance] NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

theorem native_specialized_absorbed_exact
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AbelianScheme.CentralAction.Interface.Construction.ActionData D) (hA : AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
    (res : AbelianScheme.TateComparison.Data.modelRing K D.denominator →+* ZMod q)
    (hres : res.comp (algebraMap (NumberField.RingOfIntegers K)
      (AbelianScheme.TateComparison.Data.modelRing K D.denominator)) = j.residue)
    (side : Fin s → Bool)
    (hp : HeckeCycles.Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q
      (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (HeckeCycles.ComparisonPolynomial.CM.sourceGroup D res).X)
      (fun i => HeckeCycles.Intrinsic.EquationData.CM.IntrinsicPoints.operator D hg j hq.2.2.2.1 res hres
        (A.TAlb (HeckeCycles.Neighbor.Types.CM.integralType D.reference.distinguished side i)))) :
    type_of% (HeckeCycles.Intrinsic.Polynomial.CM.IntrinsicTransport.specialized_polynomial (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q)
      D hg j hq.2.2.2.1 res hres (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hA j)
      (NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A side)
      (fun i => A.TAlb (HeckeCycles.Neighbor.Types.CM.integralType D.reference.distinguished side i))
      (fun i => AbsorbedOperators.native_absorbed_integral D hg hq hIsogenyQuotient A hA j side i) hp) :=
  HeckeCycles.Intrinsic.Polynomial.CM.IntrinsicTransport.specialized_polynomial (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q)
    D hg j hq.2.2.2.1 res hres (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hA j)
    (NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A side)
    (fun i => A.TAlb (HeckeCycles.Neighbor.Types.CM.integralType D.reference.distinguished side i))
    (fun i => AbsorbedOperators.native_absorbed_integral D hg hq hIsogenyQuotient A hA j side i) hp

theorem native_specialized_absorbed_polynomial
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AbelianScheme.CentralAction.Interface.Construction.ActionData D) (hA : AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
    (res : AbelianScheme.TateComparison.Data.modelRing K D.denominator →+* ZMod q)
    (hres : res.comp (algebraMap (NumberField.RingOfIntegers K)
      (AbelianScheme.TateComparison.Data.modelRing K D.denominator)) = j.residue)
    (side : Fin s → Bool)
    (hp : HeckeCycles.Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q
      (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (HeckeCycles.ComparisonPolynomial.CM.sourceGroup D res).X)
      (fun i => HeckeCycles.Intrinsic.EquationData.CM.IntrinsicPoints.operator D hg j hq.2.2.2.1 res hres
        (A.TAlb (HeckeCycles.Neighbor.Types.CM.integralType D.reference.distinguished side i)))) :
    SpecializedPolynomialPredicate.Intrinsic.SpecializedOrdinaryPolynomial (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j)
      (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hA j) (NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A side) :=
  SpecializedPolynomialPredicate.Intrinsic.specializedOrdinaryPolynomial_intro
    (HeckeCycles.AlbaneseModel.CM.comparisonModel D hg j hq.2.2.2.1)
    (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hA j) (NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A side)
    (native_specialized_absorbed_exact D hg hq hIsogenyQuotient A hA j res hres side hp)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SpecializedPolynomial

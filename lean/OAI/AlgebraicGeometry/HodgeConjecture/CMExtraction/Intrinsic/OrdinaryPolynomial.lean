import OAI.NumberTheory.PadicHodge.IntrinsicParameters
import OAI.NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot

/-! # Ordinary Polynomial -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OrdinaryPolynomial

noncomputable section

section

/-! Name the exact ordinary Hecke polynomial proposition so native-datum
specializations compare the model and action before expanding its formula. -/

open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic

attribute [local instance] NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

def NativeOrdinaryPolynomial
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)
    (side : Fin s → Bool) (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q) : Prop :=
  ∀ (A : AbelianScheme.CentralAction.Interface.Construction.ActionData D) (hA : AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A),
    HeckeCycles.Ordinary.Polynomial.CM.heckePolynomialValue q
      (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j).specialFiber.scheme)
      (fun i => HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j)
        (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hA j) (NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A side i)) = 0

end

/-! Transport the full ordinary polynomial along an equality of Hecke
models, retaining the dependent local embedding. -/

theorem native_ordinary_polynomial_transport
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D₁ D₂ : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hD : D₁ = D₂)
    (side : Fin s → Bool)
    (j₁ : PELModuli.CMPoints.Arithmetic.QadicChoice K D₁.complexEmbedding q)
    (j₂ : PELModuli.CMPoints.Arithmetic.QadicChoice K D₂.complexEmbedding q) (hj : HEq j₁ j₂)
    (hp : ∀ (hg : D₁.HasIntegralModelGeometry) (hq : D₁.IsGoodCompletelySplitPrime)
      (hIsogenyQuotient : D₁.RealizesIsogenyQuotient), NativeOrdinaryPolynomial D₁ hg hq hIsogenyQuotient side j₁) :
    ∀ (hg : D₂.HasIntegralModelGeometry) (hq : D₂.IsGoodCompletelySplitPrime)
      (hIsogenyQuotient : D₂.RealizesIsogenyQuotient), NativeOrdinaryPolynomial D₂ hg hq hIsogenyQuotient side j₂ := by
  cases hD
  cases hj
  exact hp

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OrdinaryPolynomial

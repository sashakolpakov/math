import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ComparisonIntrinsicClass
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Albanese
import OAI.NumberTheory.PadicHodge.IntrinsicModel

/-! # Comparison Filtration -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ComparisonFiltration

noncomputable section

/-! The actual Albanese presentation and Betti equivalence at the chosen
comparison embedding, with the native Hodge filtration identified. -/

open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q)

def nativeComparisonProjectiveAt (κ : K →+* ℂ) (hκ : κ = D.pel.complexEmbedding) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation ((NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D.pel hg hq j).complexFiber κ).scheme.left
      ((NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D.pel hg hq j).complexFiber κ).scheme.hom :=
  hκ.symm ▸ Albanese.nativeAlbaneseProjectiveOfGeometry D hg

def nativeComparisonEquivAt (κ : K →+* ℂ) (hκ : κ = D.pel.complexEmbedding) :
    ComplexMultiplication.WeightOne.CM.Complexification D.pel.H1 ≃ₗ[ℂ] (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D.pel hg hq j).ComplexBetti κ :=
  hκ.symm ▸ ComparisonBetti.Intrinsic.nativeBettiComplexification D hg

def nativeComparisonProjective := nativeComparisonProjectiveAt D hg hq j
  (j.complexClosure.comp j.fieldInClosure) j.complex_compatibility

def nativeComparisonEquiv := nativeComparisonEquivAt D hg hq j
  (j.complexClosure.comp j.fieldInClosure) j.complex_compatibility

theorem native_comparison_filtration_at (hHodgeDecomposition : Mem.HodgeDecompositionInput)
    (κ : K →+* ℂ) (hκ : κ = D.pel.complexEmbedding) :
    (Base.nativeH1 D hHodgeDecomposition hg).holomorphic.map (nativeComparisonEquivAt D hg hq j κ hκ).toLinearMap =
      (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D.pel hg hq j).bettiFiltration κ (nativeComparisonProjectiveAt D hg hq j κ hκ) 1 := by
  subst κ
  exact ComparisonIntrinsicClass.Intrinsic.native_holomorphic_complex_image D hHodgeDecomposition hg (Albanese.nativeAlbaneseProjectiveOfGeometry D hg)

theorem native_comparison_filtration (hHodgeDecomposition : Mem.HodgeDecompositionInput) :
    (Base.nativeH1 D hHodgeDecomposition hg).holomorphic.map (nativeComparisonEquiv D hg hq j).toLinearMap =
      (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D.pel hg hq j).bettiFiltration (j.complexClosure.comp j.fieldInClosure)
        (nativeComparisonProjective D hg hq j) 1 :=
  native_comparison_filtration_at D hg hq j hHodgeDecomposition _ j.complex_compatibility

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ComparisonFiltration

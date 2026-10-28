import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ComparisonFiltration
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Comparison

/-! # Comparison Range -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ComparisonRange

noncomputable section

/-! Transport native generalized character spaces through the exact Betti
equivalence used by the comparison model, including its chosen embedding. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors
open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Comparison

attribute [local instance] NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q)
  (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
  (R : (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D.pel hg hq j).HeckeRealization (AbelianScheme.TateComparison.HeckeKernel.Hecke s q))
  (hR : (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D.pel hg hq j).bettiHecke D.pel.complexEmbedding R =
    (fun h => A.cohomologyAction h))

include hElementaryDivisors hR in
theorem native_comparison_range_at
    (κ : K →+* ℂ) (hκ : κ = D.pel.complexEmbedding)
    (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification D.pel.H1)) (χ : AbelianScheme.TateComparison.HeckeKernel.Hecke s q → ℂ)
    (hP : LinearMap.range P = HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (A.cohomologyAction h).baseChange ℂ) χ) :
    LinearMap.range ((ComparisonFiltration.nativeComparisonEquivAt D hg hq j κ hκ).conj P) =
      (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D.pel hg hq j).bettiHeckeSummand κ R χ := by
  subst κ
  change LinearMap.range ((ComparisonBetti.Intrinsic.nativeBettiComplexification D hg).conj P) = _
  rw [SummandTransport.Comparison.conjugate_range, hP]
  exact SummandTransport.Comparison.jointSpace_map_equiv (ComparisonBetti.Intrinsic.nativeBettiComplexification D hg) _ _
    (Comparison.Intrinsic.native_full_comparison_intertwining D hg hq A hElementaryDivisors j R hR) χ

include hElementaryDivisors hR in
theorem native_comparison_range
    (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification D.pel.H1)) (χ : AbelianScheme.TateComparison.HeckeKernel.Hecke s q → ℂ)
    (hP : LinearMap.range P = HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (A.cohomologyAction h).baseChange ℂ) χ) :
    LinearMap.range ((ComparisonFiltration.nativeComparisonEquiv D hg hq j).conj P) =
      (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D.pel hg hq j).bettiHeckeSummand (j.complexClosure.comp j.fieldInClosure) R χ :=
  native_comparison_range_at D hg hq j A hElementaryDivisors R hR _ j.complex_compatibility P χ hP

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ComparisonRange

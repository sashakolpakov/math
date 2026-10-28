import OAI.AlgebraicGeometry.HodgeConjecture.BalancedMonomials
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.MultilinearTransfer

/-! # Line Transfer -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.LineTransfer.CM.Construction

noncomputable section

/-! The separate selected-line maps supplied by the CM decomposition,
in the actual algebraic pullback spans of their realizations. -/

open _root_.CategoryTheory
open scoped TensorProduct

theorem realized_lineTransfer_mem
    (hfullness : ComplexMultiplication.KnownAlgebraicity.CM.KnownResults.RationalH1MapsAreAlgebraic)
    {A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)}
    (D : ComplexMultiplication.Decomposition.CM.CMDecomposition H)
    (hhol : H.holomorphic = A.h1Holomorphic) (hanti : H.antiholomorphic = A.h1Antiholomorphic)
    (j : D.EmbeddingIndex) (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (D.embeddingLineSource j)) :
    (D.embeddingLineTransfer j).comp (R.comparison.symm.toLinearMap.baseChange ℂ) ∈
      R.abelianVariety.algebraicH1PullbackSpan A := by
  apply ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.rationalHodgeMapSpan_le_algebraicH1PullbackSpan
    hfullness R.abelianVariety A R.h1HodgeStructure H
    R.h1HodgeStructure_holomorphic R.h1HodgeStructure_antiholomorphic hhol hanti
  exact BalancedMonomials.precompose_realization_mem_hodge_span R (D.embeddingLineTransfer j)
    (D.embeddingLineTransfer_mem_rationalHodgeMapSpan j)

theorem realized_lineTransfer_basis
    {A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)}
    (D : ComplexMultiplication.Decomposition.CM.CMDecomposition H) (j : D.EmbeddingIndex) (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (D.embeddingLineSource j)) :
    (D.embeddingLineTransfer j).comp (R.comparison.symm.toLinearMap.baseChange ℂ)
      (R.comparison.toLinearMap.baseChange ℂ
        ((D.embeddingLineSource_cm j).embeddingBasis
          (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv D.commonCoefficientField 1))) =
      D.embeddingBasis j := by
  rw [LinearMap.comp_apply]
  change D.embeddingLineTransfer j
    ((R.comparison.baseChange ℚ ℂ _ _).symm ((R.comparison.baseChange ℚ ℂ _ _) _)) = _
  rw [LinearEquiv.symm_apply_apply, D.embeddingLineTransfer_basis, ite_eq_left rfl]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.LineTransfer.CM.Construction

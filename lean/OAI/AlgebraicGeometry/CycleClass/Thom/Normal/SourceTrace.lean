import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizedLocalTrace
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceCompactGysin

/-! # Source Trace -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SourceTrace

noncomputable section

/-! The actual normal-chart source Gysin map preserves fundamental traces
in arbitrary codimension. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceCompactGysin.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizedLocalTrace.Constructions
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions.HigherThom

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
variable (x : Z.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ) Z.regularComplementInclusion x)

abbrev regularSourceGysinTopDegree : 2 * p + 2 * Z.regularComplexDimension = 2 * V.complexDimension := by
  have h := Z.regularComplexDimension_add_codimension
  omega

theorem regularNormalPairSourceCompactGysin_topTrace
    (hq : ContMDiffOn 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ))
      𝓘(ℂ, V.analyticModel) ∞ P.ambientChart.symm P.ambientChart.target)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding))
      (2 * Z.regularComplexDimension)) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace V.complexDimension (M := P.openNeighborhood)
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood))
        (regularSourceGysinTopDegree V Z))
        (HodgeConjecture.DegreeTwo.SourceCompactGysin.Constructions.normalPairSourceCompactGysin P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding
          (2 * Z.regularComplexDimension) a)) =
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace Z.regularComplexDimension
        (M := HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding) a := by
  let hf := Z.isClosedEmbedding_regularComplementInclusion.isEmbedding
  let e := AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
    (X := TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (Y := TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentBallOpen P))
    (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf) (2 * Z.regularComplexDimension)
  have hdim : p + Z.regularComplexDimension = V.complexDimension :=
    (Nat.add_comm p Z.regularComplexDimension).trans Z.regularComplexDimension_add_codimension
  have ht := NormalizedLocalTrace.Constructions.normalPairCompactGysinTop_trace_normalized P hdim hq hqi (e.inv a)
  change AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace V.complexDimension (M := P.openNeighborhood)
    (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood))
      (congrArg (fun n => 2 * n) hdim)) (HodgeConjecture.DegreeTwo.RegularLocalGysinTrace.Constructions.normalPairSourceCompactGysinTop P hf a)) = _ at ht
  rw [← HodgeConjecture.DegreeTwo.SourceCompactGysin.Constructions.normalPairSourceCompactGysin_top,
    HodgeConjecture.DegreeTwo.CompactCupEvaluation.Constructions.compactCohomologyDegreeCast_trans (TopCat.of P.neighborhood)
      (Nat.mul_add 2 p Z.regularComplexDimension).symm (congrArg (fun n => 2 * n) hdim)
      (regularSourceGysinTopDegree V Z)] at ht
  have hs := HodgeConjecture.DegreeTwo.RegularLocalGysinTrace.Constructions.moduleIso_trace_inverse_apply e
    (AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace Z.regularComplexDimension (M := HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentBallOpen P))
    (AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace Z.regularComplexDimension (M := HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))
    (HodgeConjecture.DegreeTwo.NormalPairSourceTrace.Constructions.normalPairSourceHomeomorph_nativeTrace P hf (Z.contMDiff_regularComplementInclusion ∞)
      (fun y => HodgeConjecture.DegreeTwo.ImmersionSmoothPullback.Constructions.immersionAt_of_order_le (by simp) (Z.regularComplement_isImmersionAt y)) hq hqi) a
  exact ht.trans hs

end Constructions.HigherThom

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SourceTrace

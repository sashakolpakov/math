import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.Trace
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.RationalCompactFundamental
import OAI.AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality

/-! # Trace Stage -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.TraceStage

noncomputable section

/-! Compact-stage meaning of the actual closed-immersion fundamental trace. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality.Cycles OAI.AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions.Construction

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (D : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)

theorem fundamentalTrace_stage
    (K : Compacts D.regularAmbientSpace)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (K : Set D.regularAmbientSpace)ᶜ (2 * D.regularComplexDimension)) :
    Trace.Constructions.Construction.fundamentalTrace D
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace) K
        (2 * D.regularComplexDimension) b) =
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of D.regularAnalyticSpace)
      (D.regularComplementTopCatMap ⁻¹' (K : Set D.regularAmbientSpace))ᶜ
      (2 * D.regularComplexDimension)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) D.regularComplementTopCatMap
        (A := (D.regularComplementTopCatMap ⁻¹' (K : Set D.regularAmbientSpace))ᶜ)
        (B := (K : Set D.regularAmbientSpace)ᶜ) (fun _ hx => hx)
        (2 * D.regularComplexDimension) b)
      (Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass D.regularComplexDimension
        (D.regularComplementTopCatMap ⁻¹' (K : Set D.regularAmbientSpace))
        (D.isProperMap_regularComplementTopCatMap.isCompact_preimage K.isCompact)) := by
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportCohomologyι_properPullback (ModuleCat.of ℚ ℚ) D.regularComplementTopCatMap
      D.isProperMap_regularComplementTopCatMap K (2 * D.regularComplexDimension)) b
  change AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace D.regularComplexDimension
    (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ) D.regularComplementTopCatMap
      D.isProperMap_regularComplementTopCatMap (2 * D.regularComplexDimension)
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace) K
        (2 * D.regularComplexDimension) b)) = _
  exact (congrArg (AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace D.regularComplexDimension (M := D.regularAnalyticSpace)) h).trans
    (AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace_stage_apply D.regularComplexDimension (M := D.regularAnalyticSpace)
      (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.properCompactPreimage D.regularComplementTopCatMap D.isProperMap_regularComplementTopCatMap K)
      (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback (ModuleCat.of ℚ ℚ) D.regularComplementTopCatMap
        D.isProperMap_regularComplementTopCatMap K (2 * D.regularComplexDimension) b))

/-- The compact trace evaluates on the actual rational relative pushforward
of the source's independently constructed compact fundamental class. -/
theorem fundamentalTrace_stage_rationalPushforward
    (K : Compacts D.regularAmbientSpace)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (K : Set D.regularAmbientSpace)ᶜ (2 * D.regularComplexDimension)) :
    Trace.Constructions.Construction.fundamentalTrace D
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace) K
        (2 * D.regularComplexDimension) b) =
    Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of D.regularAmbientSpace)
      (K : Set D.regularAmbientSpace)ᶜ (2 * D.regularComplexDimension) b
      (HomologicalComplex.homologyMap
        (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ D.regularComplementTopCatMap
          (A := (D.regularComplementTopCatMap ⁻¹' (K : Set D.regularAmbientSpace))ᶜ)
          (B := (K : Set D.regularAmbientSpace)ᶜ) (fun _ hx => hx))
        (2 * D.regularComplexDimension)
        (ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass D.regularComplexDimension
          (D.regularComplementTopCatMap ⁻¹' (K : Set D.regularAmbientSpace))
          (D.isProperMap_regularComplementTopCatMap.isCompact_preimage K.isCompact))) := by
  rw [fundamentalTrace_stage, AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.relativeRationalHomologyEvaluation_eq_scalarEvaluation]
  exact Geometric.RelativeUniversalCoefficientNaturality.Cycles.relativeHomologyEvaluation_naturality (ModuleCat.of ℚ ℚ) D.regularComplementTopCatMap
    (fun _ hx => hx) (2 * D.regularComplexDimension) b _

end Constructions.Construction

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.TraceStage

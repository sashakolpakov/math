import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PairSmoothSourceChart
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PairIntrinsicTraceDimension
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicImmersionNormalPair

/-! # Normal Pair Source Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairSourceTrace.Constructions

noncomputable section

/-! The tangent integral is the native fundamental trace on the embedded source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicImmersionNormalPair
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

theorem normalPairSourceHomeomorph_nativeTrace
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {d p c : ℕ}
    [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin p → ℂ) N]
    [T2Space M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]
    {f : M → N} {x : M}
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x) (hf : Topology.IsEmbedding f)
    (hfs : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) ∞ f)
    (himm : ∀ y, Manifold.IsImmersionAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) ∞ f y)
    (hq : ContMDiffOn 𝓘(ℂ, Fin p → ℂ)
      𝓘(ℂ, (Fin d → ℂ) × (Fin c → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, (Fin d → ℂ) × (Fin c → ℂ))
      𝓘(ℂ, Fin p → ℂ) ∞ P.ambientChart.symm P.ambientChart.target) :
    (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
      (X := TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentBallOpen P))
      (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf) (2*d)).hom ≫
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := NormalPairProductSupport.Constructions.normalPairSourceOpen P hf) =
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := NormalPairProductSupport.Constructions.normalPairTangentBallOpen P) :=
  AlgebraicTopology.Duality.Poincare.ComplexManifoldTraceDimension.complexManifoldTrace_homeomorphIso d (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf)
    ((PairSmoothSourceChart.Constructions.normalPairSourceHomeomorph_contMDiff P hf hfs hq).of_le (by simp))
    ((PairSmoothSourceChart.Constructions.normalPairSourceHomeomorph_symm_contMDiff P hf himm hqi).of_le (by simp))

theorem regularNormalPairSourceHomeomorph_nativeTrace
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
    (x : Z.regularAnalyticSpace)
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ) Z.regularComplementInclusion x)
    (hq : ContMDiffOn 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ))
      𝓘(ℂ, V.analyticModel) ∞ P.ambientChart.symm P.ambientChart.target) :
    (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
      (X := TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding))
      (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentBallOpen P))
      (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)
      (2*Z.regularComplexDimension)).hom ≫
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace Z.regularComplexDimension
        (M := NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding) =
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace Z.regularComplexDimension (M := NormalPairProductSupport.Constructions.normalPairTangentBallOpen P) :=
  normalPairSourceHomeomorph_nativeTrace P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding
    (Z.contMDiff_regularComplementInclusion ∞)
    (fun y => ImmersionSmoothPullback.Constructions.immersionAt_of_order_le (by simp) (Z.regularComplement_isImmersionAt y)) hq hqi

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairSourceTrace.Constructions

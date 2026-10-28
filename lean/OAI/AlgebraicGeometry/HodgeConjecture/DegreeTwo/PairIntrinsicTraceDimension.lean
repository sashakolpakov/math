import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairIntrinsicTrace
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SectionSmoothFixedPair

/-! # Pair Intrinsic Trace Dimension -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PairIntrinsicTraceDimension.Constructions

noncomputable section

/-! The native normal-pair trace in the actual ambient complex dimension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

theorem normalPairCompactGysinTop_nativeTrace_dimension
    {M N : Type} [TopologicalSpace N] {c d p : ℕ} {f : M → N} {x : M}
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x)
    [ChartedSpace (Fin p → ℂ) N] [T2Space N] [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 N]
    (hdim : c+d = p)
    (hq : ContMDiffOn 𝓘(ℂ, Fin p → ℂ)
      𝓘(ℂ, (Fin d → ℂ) × (Fin c → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, (Fin d → ℂ) × (Fin c → ℂ))
      𝓘(ℂ, Fin p → ℂ) ∞ P.ambientChart.symm P.ambientChart.target)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) (2*d)) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace p (M := P.openNeighborhood)
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood))
        (congrArg (fun n => 2*n) hdim)) (NormalPairIntrinsicTrace.Constructions.normalPairCompactGysinTop P a)) =
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := NormalPairIntrinsicTrace.Constructions.normalPairTangentOpen P) a * LocalProductCoefficient.Constructions.localProductCupCoefficient c d := by
  subst p
  simpa only [eqToHom_refl, CategoryTheory.id_apply] using
    NormalPairIntrinsicTrace.Constructions.normalPairCompactGysinTop_nativeTrace P hq hqi a

theorem regularNormalPairCompactGysinTop_nativeTrace
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
    (x : Z.regularAnalyticSpace)
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ) Z.regularComplementInclusion x)
    (hq : ContMDiffOn 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ))
      𝓘(ℂ, V.analyticModel) ∞ P.ambientChart.symm P.ambientChart.target)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) (2*Z.regularComplexDimension)) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace V.complexDimension (M := P.openNeighborhood)
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood))
        (congrArg (fun n => 2*n)
          ((Nat.add_comm 1 Z.regularComplexDimension).trans Z.regularComplexDimension_add_codimension)))
        (NormalPairIntrinsicTrace.Constructions.normalPairCompactGysinTop P a)) =
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace Z.regularComplexDimension (M := NormalPairIntrinsicTrace.Constructions.normalPairTangentOpen P) a *
      LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension :=
  normalPairCompactGysinTop_nativeTrace_dimension P
    ((Nat.add_comm 1 Z.regularComplexDimension).trans Z.regularComplexDimension_add_codimension) hq hqi a

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PairIntrinsicTraceDimension.Constructions

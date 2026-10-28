import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceGysinProjection
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactCupEvaluation

/-! # Source Gysin Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceGysinTrace.Constructions

noncomputable section

/-! Exact degree transport for the actual source Gysin map and its native top trace. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

theorem normalPairSourceCompactGysin_degreeCast
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {c d : ℕ}
    {f : M → N} {x : M}
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x) (hf : Topology.IsEmbedding f)
    {p q : ℕ} (h : p=q)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) p) :
    eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood))
      (congrArg (fun n => 2*c+n) h)) (SourceCompactGysin.Constructions.normalPairSourceCompactGysin P hf p a) =
    SourceCompactGysin.Constructions.normalPairSourceCompactGysin P hf q
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf))) h) a) := by
  subst q
  rfl

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1) (x : Z.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ) Z.regularComplementInclusion x)

abbrev regularSourceGysinTopDegree : 2*1+2*Z.regularComplexDimension=2*V.complexDimension :=
  (Nat.mul_add 2 1 Z.regularComplexDimension).symm.trans (RegularLocalGysinTrace.Constructions.regularNormalPairDegreeEq V Z)

theorem regularNormalPairSourceCompactGysin_topTrace
    (hq : ContMDiffOn 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ))
      𝓘(ℂ, V.analyticModel) ∞ P.ambientChart.symm P.ambientChart.target)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding))
      (2*Z.regularComplexDimension)) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace V.complexDimension (M := P.openNeighborhood)
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood))
        (regularSourceGysinTopDegree V Z))
        (SourceCompactGysin.Constructions.normalPairSourceCompactGysin P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding
          (2*Z.regularComplexDimension) a)) =
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace Z.regularComplexDimension
        (M := NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding) a *
        LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension := by
  have ht := RegularLocalGysinTrace.Constructions.regularNormalPairSourceGysin_nativeTrace V Z x P hq hqi a
  rw [← SourceCompactGysin.Constructions.normalPairSourceCompactGysin_top] at ht
  rw [CompactCupEvaluation.Constructions.compactCohomologyDegreeCast_trans (TopCat.of P.neighborhood)
    (Nat.mul_add 2 1 Z.regularComplexDimension).symm (RegularLocalGysinTrace.Constructions.regularNormalPairDegreeEq V Z)
    (regularSourceGysinTopDegree V Z)] at ht
  exact ht

theorem regularNormalPairSourceCompactGysin_trace_in_degree
    (hq : ContMDiffOn 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ))
      𝓘(ℂ, V.analyticModel) ∞ P.ambientChart.symm P.ambientChart.target)
    (s : ℕ) (hs : s=2*Z.regularComplexDimension) (ht : 2*1+s=2*V.complexDimension)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)) s) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace V.complexDimension (M := P.openNeighborhood)
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)) ht)
        (SourceCompactGysin.Constructions.normalPairSourceCompactGysin P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding s a)) =
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace Z.regularComplexDimension
      (M := NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding))) hs) a) *
      LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension := by
  subst s
  exact regularNormalPairSourceCompactGysin_topTrace V Z x P hq hqi a

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceGysinTrace.Constructions

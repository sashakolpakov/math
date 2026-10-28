import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceGysinTrace
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicGysinAdjunction

/-! # Source Gysin Intrinsic Adjunction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceGysinIntrinsicAdjunction.Constructions

noncomputable section

/-! The actual local Thom Gysin map is adjoint to actual source restriction under native evaluation. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1) (x : Z.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ) Z.regularComplementInclusion x)

theorem regularSourceGysinPairingDegree (q r : ℕ) (hs : q+r=2*Z.regularComplexDimension) :
    (2*1+q)+r=2*V.complexDimension := by
  have h := SourceGysinTrace.Constructions.regularSourceGysinTopDegree V Z
  omega

theorem regularNormalPairSourceCompactGysin_adjunction
    (hq : ContMDiffOn 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ))
      𝓘(ℂ, V.analyticModel) ∞ P.ambientChart.symm P.ambientChart.target)
    (q r : ℕ) (hs : q+r=2*Z.regularComplexDimension)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)) q)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) r) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension (M := P.openNeighborhood) r (2*1+q)
      (by have h := regularSourceGysinPairingDegree V Z q r hs; omega) b
      (SourceCompactGysin.Constructions.normalPairSourceCompactGysin P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding q a) =
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation Z.regularComplexDimension
      (M := NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding) r q (by omega)
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
        (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding) r b) a *
      LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension := by
  let hf := Z.isClosedEmbedding_regularComplementInclusion.isEmbedding
  have ht := regularSourceGysinPairingDegree V Z q r hs
  have htop : 2*1+(q+r)=2*V.complexDimension := by omega
  have hL := CompactCupTrace.Constructions.compactCohomologyRightCup_trace V.complexDimension (M := P.openNeighborhood)
    (2*1+q) r ht b (SourceCompactGysin.Constructions.normalPairSourceCompactGysin P hf q a)
  have hR := CompactCupTrace.Constructions.compactCohomologyRightCup_trace Z.regularComplexDimension
    (M := NormalPairProductSupport.Constructions.normalPairSourceOpen P hf) q r hs
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) r b) a
  have hp := congrArg (fun z => AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace V.complexDimension (M := P.openNeighborhood)
    (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)) htop) z))
    (SourceGysinProjection.Constructions.normalPairSourceCompactGysin_projection P hf q r a b)
  have hd := congrArg (AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace V.complexDimension (M := P.openNeighborhood))
    (CompactCupEvaluation.Constructions.compactCohomologyDegreeCast_trans (TopCat.of P.neighborhood) (Nat.add_assoc (2*1) q r) htop ht
      (CompactCohomologyCup.Constructions.compactCohomologyRightCup (TopCat.of P.neighborhood) (2*1+q) r b
        (SourceCompactGysin.Constructions.normalPairSourceCompactGysin P hf q a)))
  have hT := SourceGysinTrace.Constructions.regularNormalPairSourceCompactGysin_trace_in_degree V Z x P hq hqi (q+r) hs htop
    (CompactCohomologyCup.Constructions.compactCohomologyRightCup (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) q r
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) r b) a)
  exact hL.symm.trans (hd.symm.trans (hp.trans (hT.trans
    (congrArg (fun z => z * LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension) hR))))

theorem regularNormalPairSourceCompactGysin_eq_native
    (hq : ContMDiffOn 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ))
      𝓘(ℂ, V.analyticModel) ∞ P.ambientChart.symm P.ambientChart.target)
    (q r : ℕ) (hs : q+r=2*Z.regularComplexDimension)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)) q) :
    SourceCompactGysin.Constructions.normalPairSourceCompactGysin P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding q a =
      LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension •
        IntrinsicGysinAdjunction.Constructions.nativeCompactCohomologyPushforward
          (M := NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)
          (N := P.openNeighborhood) (d := Z.regularComplexDimension) (e := V.complexDimension)
          (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)
          q (2*1+q) r hs (regularSourceGysinPairingDegree V Z q r hs) a := by
  have ht := regularSourceGysinPairingDegree V Z q r hs
  apply (AlgebraicTopology.Duality.Poincare.CompactSupportAnd.compactSupport_eq_iff_evaluation_eq V.complexDimension
    (M := P.openNeighborhood) r (2*1+q) (by omega) _ _).mpr
  intro b
  rw [map_smul, regularNormalPairSourceCompactGysin_adjunction V Z x P hq hqi q r hs]
  rw [IntrinsicGysinAdjunction.Constructions.nativeCompactCohomologyPushforward_adjunction]
  exact mul_comm _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceGysinIntrinsicAdjunction.Constructions

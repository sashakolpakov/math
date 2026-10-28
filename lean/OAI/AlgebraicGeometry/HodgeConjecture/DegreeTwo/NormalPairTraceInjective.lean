import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PairIntrinsicTraceDimension
import OAI.AlgebraicTopology.Duality.Poincare.EuclideanChart

/-! # Normal Pair Trace Injective -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairTraceInjective.Constructions

noncomputable section

/-! The native top trace determines actual compact classes on every normal neighborhood. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.EuclideanChart
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

theorem complexManifoldTrace_isIso_of_euclidean (p : ℕ) {N : Type} [TopologicalSpace N]
    [T2Space N] [ChartedSpace (Fin p → ℂ) N] [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 N]
    (e : N ≃ₜ (Fin p → ℂ)) : IsIso (AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace p (M := N)) := by
  let : PathConnectedSpace N := e.symm.surjective.pathConnectedSpace e.symm.continuous
  let : IsIso (AlgebraicTopology.Duality.Poincare.ComplexManifoldCap.complexManifoldCompactSupportCap p (M := N) (2*p) 0 rfl) :=
    AlgebraicTopology.Duality.Poincare.EuclideanChart.euclideanChartCap_top_isIso p e
  let : IsIso (AlgebraicTopology.Duality.Poincare.CapAugmentation.rationalH0Augmentation (TopCat.of N)) := by
    change IsIso ((TopCat.of N).singularHomology₀ε (C := ModuleCat.{0} ℚ) (ModuleCat.of ℚ ℚ))
    infer_instance
  unfold AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace
  infer_instance

def normalPairEuclideanHomeomorph {M N : Type} [TopologicalSpace N] {c d : ℕ} {f : M → N} {x : M}
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x) :
    P.openNeighborhood ≃ₜ (Fin (c+d) → ℂ) :=
  (NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P).trans
    (((CycleClass.Geometric.NormalProductCohomology.Cycles.normalOpenBallHomeomorph (Fin c → ℂ) P.radius P.radius_pos).symm.prodCongr
      (CycleClass.Geometric.NormalProductCohomology.Cycles.normalOpenBallHomeomorph (Fin d → ℂ) P.radius P.radius_pos).symm).trans
        (LocalProductCoefficient.Constructions.productFlattenCoordinates c d).toHomeomorph)

theorem normalPair_nativeTrace_isIso {M N : Type} [TopologicalSpace N] {c d p : ℕ} {f : M → N} {x : M}
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x)
    [T2Space N] [ChartedSpace (Fin p → ℂ) N] [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 N]
    (hdim : c+d=p) : IsIso (AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace p (M := P.openNeighborhood)) := by
  subst p
  exact complexManifoldTrace_isIso_of_euclidean (c+d) (normalPairEuclideanHomeomorph P)

theorem normalPair_nativeTrace_injective {M N : Type} [TopologicalSpace N] {c d p : ℕ} {f : M → N} {x : M}
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x)
    [T2Space N] [ChartedSpace (Fin p → ℂ) N] [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 N]
    (hdim : c+d=p) : Function.Injective (AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace p (M := P.openNeighborhood)) := by
  let := normalPair_nativeTrace_isIso P hdim
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairTraceInjective.Constructions

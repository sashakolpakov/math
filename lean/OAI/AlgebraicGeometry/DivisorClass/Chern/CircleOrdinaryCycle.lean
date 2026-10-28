import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmallCirclePositiveCycle
import OAI.AlgebraicGeometry.DivisorClass.Chern.CircleArcWinding
import OAI.AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import OAI.AlgebraicTopology.Duality.Poincare.RelativeCochainDual

/-! # Circle Ordinary Cycle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CircleOrdinaryCycle

noncomputable section

/-! The actual small positive circle, its ordinary chain, and its winding. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality OAI.AlgebraicTopology.Duality.Poincare.RelativeCochainDual
open scoped Simplicial

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem integralEdgeChain_map {X Y : TopCat.{0}} (f : X ⟶ Y)
    (c : C(Convexity.StdSimplex ℝ (Fin 2), X)) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f).f 1 (CircleArcWinding.integralEdgeChain X c) =
      CircleArcWinding.integralEdgeChain Y (f.hom.comp c) := by
  have h := ConcreteCategory.congr_hom (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X)
    (TopCat.toSSet.obj Y) (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)
    ((X.toSSetObjEquiv _).symm c)) 1
  refine h.trans ?_
  congr 1

def positiveCircleOrdinaryCycle : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle) 1 :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart)
    1 SmallCirclePositiveCycle.positiveCircleSmallCycle

theorem positiveCircleOrdinaryCycle_chain :
    positiveCircleOrdinaryCycle.val =
      CircleArcWinding.integralEdgeChain CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle CirclePositiveArcs.positiveWestArcMap +
        CircleArcWinding.integralEdgeChain CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle CirclePositiveArcs.positiveEastArcMap := by
  let S := CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart
  let j := CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart
  let CU := CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart)
  let CV := CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart)
  have hl : (biprod.inl : CU ⟶ CU ⊞ CV) ≫ S.g ≫ j =
      CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart) := by
    rw [CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence_g, biprod.inl_desc_assoc]
    exact CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_left _ _ _
  have hr : (biprod.inr : CV ⟶ CU ⊞ CV) ≫ S.g ≫ j =
      CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart) := by
    rw [CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence_g, biprod.inr_desc_assoc]
    exact CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_right _ _ _
  have hL := ConcreteCategory.congr_hom (congrArg (fun f => f.f 1) hl)
    (CircleArcWinding.integralEdgeChain (TopCat.of CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart) CircleArcWinding.positiveWestChartArc)
  have hR := ConcreteCategory.congr_hom (congrArg (fun f => f.f 1) hr)
    (CircleArcWinding.integralEdgeChain (TopCat.of CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart) CircleArcWinding.positiveEastChartArc)
  change j.f 1 (S.g.f 1 ((biprod.inl : CU ⟶ CU ⊞ CV).f 1 _ +
    (biprod.inr : CV ⟶ CU ⊞ CV).f 1 _)) = _
  rw [map_add, map_add]
  change j.f 1 (S.g.f 1 ((biprod.inl : CU ⟶ CU ⊞ CV).f 1 _)) = _ at hL
  change j.f 1 (S.g.f 1 ((biprod.inr : CV ⟶ CU ⊞ CV).f 1 _)) = _ at hR
  rw [hL, hR, integralEdgeChain_map, integralEdgeChain_map]
  rfl

theorem positiveCircleOrdinaryCycle_winding :
    AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle) 1
      (WindingSingular.singularWindingCochain CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle CircleArcWinding.circleComplexCoordinate CircleArcWinding.circleComplexCoordinate_ne_zero)
      positiveCircleOrdinaryCycle.val = (1 : ℚ) := by
  rw [positiveCircleOrdinaryCycle_chain, map_add]
  change AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle) 1
      (WindingSingular.singularWindingCochain CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle CircleArcWinding.circleComplexCoordinate CircleArcWinding.circleComplexCoordinate_ne_zero)
      (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) _ CircleArcWinding.positiveWestCircleSimplex) +
    AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle) 1
      (WindingSingular.singularWindingCochain CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle CircleArcWinding.circleComplexCoordinate CircleArcWinding.circleComplexCoordinate_ne_zero)
      (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) _ CircleArcWinding.positiveEastCircleSimplex) = _
  rw [AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv_simplex, AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv_simplex,
    ← AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply, ← AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply,
    WindingSingular.singularWindingCochain_value, WindingSingular.singularWindingCochain_value]
  exact CircleArcWinding.positiveCircleArcs_winding

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CircleOrdinaryCycle

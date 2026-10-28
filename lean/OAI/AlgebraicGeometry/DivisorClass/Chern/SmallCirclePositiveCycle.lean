import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.DivisorClass.Chern.CircleArcWinding
import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-! # Small Circle Positive Cycle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SmallCirclePositiveCycle

noncomputable section

/-!
# ChernClass: the actual small-chain boundary of a positive circle

The two positively traversed semicircles give a cycle in the original
small-chain complex. Its native Mayer–Vietoris boundary is exactly the
negative-imaginary vertex minus the positive-imaginary vertex.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

local notation "CU" => OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of OAI.AlgebraicGeometry.CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart)
local notation "CV" => OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of OAI.AlgebraicGeometry.CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart)
local notation "S" => OAI.AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence OAI.AlgebraicGeometry.CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle OAI.AlgebraicGeometry.CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart OAI.AlgebraicGeometry.CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart
private abbrev overlapFirstChain := CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
  (CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle (Set.inter_subset_left : CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart ∩ CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart ⊆ CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart))
private abbrev overlapSecondChain := CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
  (CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle (Set.inter_subset_right : CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart ∩ CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart ⊆ CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart))
local notation "jU" => OAI.AlgebraicGeometry.DivisorClass.Chern.SmallCirclePositiveCycle.overlapFirstChain
local notation "jV" => OAI.AlgebraicGeometry.DivisorClass.Chern.SmallCirclePositiveCycle.overlapSecondChain

def positiveCircleMiddleChain : (S).X₂.X 1 :=
  (biprod.inl : CU ⟶ CU ⊞ CV).f 1 (CircleArcWinding.integralEdgeChain (TopCat.of CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart) CircleArcWinding.positiveWestChartArc) +
    (biprod.inr : CV ⟶ CU ⊞ CV).f 1 (CircleArcWinding.integralEdgeChain (TopCat.of CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart) CircleArcWinding.positiveEastChartArc)

theorem positiveWestChartArc_boundary :
    overlapFirstChain.f 0 CircleArcWinding.circleOverlapDifference =
      (CU).d 1 0 (CircleArcWinding.integralEdgeChain (TopCat.of CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart) CircleArcWinding.positiveWestChartArc) := by
  rw [CircleArcWinding.circleOverlapDifference, map_sub, CircleArcWinding.integralPointChain_map, CircleArcWinding.integralPointChain_map,
    CircleArcWinding.integralEdgeChain_boundary]
  have he : CircleArcWinding.positiveWestChartArc (Convexity.StdSimplex.single 1) =
      CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle
        (Set.inter_subset_left : CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart ∩ CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart ⊆ CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart)
        CircleArcWinding.negativeCircleOverlap := Subtype.ext CirclePositiveArcs.positiveWestArc_end
  have hs : CircleArcWinding.positiveWestChartArc (Convexity.StdSimplex.single 0) =
      CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle
        (Set.inter_subset_left : CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart ∩ CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart ⊆ CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart)
        CircleEquatorOrientation.positiveCircleOverlap := Subtype.ext CirclePositiveArcs.positiveWestArc_start
  rw [he, hs]

theorem positiveEastChartArc_boundary :
    overlapSecondChain.f 0 CircleArcWinding.circleOverlapDifference =
      -((CV).d 1 0 (CircleArcWinding.integralEdgeChain (TopCat.of CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart) CircleArcWinding.positiveEastChartArc)) := by
  rw [CircleArcWinding.circleOverlapDifference, map_sub, CircleArcWinding.integralPointChain_map, CircleArcWinding.integralPointChain_map,
    CircleArcWinding.integralEdgeChain_boundary, neg_sub]
  have he : CircleArcWinding.positiveEastChartArc (Convexity.StdSimplex.single 1) =
      CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle
        (Set.inter_subset_right : CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart ∩ CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart ⊆ CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart)
        CircleEquatorOrientation.positiveCircleOverlap := Subtype.ext CirclePositiveArcs.positiveEastArc_end
  have hs : CircleArcWinding.positiveEastChartArc (Convexity.StdSimplex.single 0) =
      CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle
        (Set.inter_subset_right : CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart ∩ CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart ⊆ CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart)
        CircleArcWinding.negativeCircleOverlap := Subtype.ext CirclePositiveArcs.positiveEastArc_start
  rw [he, hs]

/-- The original signed overlap inclusion is the boundary of the actual lift. -/
theorem positiveCircleMiddleChain_boundary :
    (S).f.f 0 CircleArcWinding.circleOverlapDifference = (S).X₂.d 1 0 positiveCircleMiddleChain := by
  have hf : (S).f = overlapFirstChain ≫ (biprod.inl : CU ⟶ CU ⊞ CV) -
      overlapSecondChain ≫ (biprod.inr : CV ⟶ CU ⊞ CV) := by
    simp only [CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence_f, biprod.lift_eq, Preadditive.neg_comp, sub_eq_add_neg]
  have hl := ConcreteCategory.congr_hom ((biprod.inl : CU ⟶ CU ⊞ CV).comm 1 0)
    (CircleArcWinding.integralEdgeChain (TopCat.of CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart) CircleArcWinding.positiveWestChartArc)
  have hr := ConcreteCategory.congr_hom ((biprod.inr : CV ⟶ CU ⊞ CV).comm 1 0)
    (CircleArcWinding.integralEdgeChain (TopCat.of CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart) CircleArcWinding.positiveEastChartArc)
  change (CU ⊞ CV).d 1 0 ((biprod.inl : CU ⟶ CU ⊞ CV).f 1 _) =
    (biprod.inl : CU ⟶ CU ⊞ CV).f 0 ((CU).d 1 0 _) at hl
  change (CU ⊞ CV).d 1 0 ((biprod.inr : CV ⟶ CU ⊞ CV).f 1 _) =
    (biprod.inr : CV ⟶ CU ⊞ CV).f 0 ((CV).d 1 0 _) at hr
  change (S).f.f 0 CircleArcWinding.circleOverlapDifference = (CU ⊞ CV).d 1 0 positiveCircleMiddleChain
  rw [positiveCircleMiddleChain, map_add, hl, hr, hf]
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f,
    ModuleCat.hom_sub, LinearMap.sub_apply, ConcreteCategory.comp_apply]
  have hL := congrArg (fun x : (CU).X 0 => (biprod.inl : CU ⟶ CU ⊞ CV).f 0 x)
    positiveWestChartArc_boundary
  have hR := congrArg (fun x : (CV).X 0 => (biprod.inr : CV ⟶ CU ⊞ CV).f 0 x)
    positiveEastChartArc_boundary
  refine (congrArg₂ (fun x y : (CU ⊞ CV).X 0 => x - y) hL hR).trans ?_
  rw [map_neg, sub_neg_eq_add]

/-- The positively traversed two-chart circle is an actual integral small cycle. -/
def positiveCircleSmallCycle : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles CycleClass.Geometric.SmallCircleHomology.Cycles.smallCircleChains 1 :=
  ⟨(S).g.f 1 positiveCircleMiddleChain, by
    rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ]
    have h := ConcreteCategory.congr_hom ((S).g.comm 1 0) positiveCircleMiddleChain
    change (S).X₃.d 1 0 ((S).g.f 1 positiveCircleMiddleChain) =
      (S).g.f 0 ((S).X₂.d 1 0 positiveCircleMiddleChain) at h
    rw [← positiveCircleMiddleChain_boundary] at h
    exact h.trans (ConcreteCategory.congr_hom
      (congrArg (fun f => f.f 0) (S).zero) CircleArcWinding.circleOverlapDifference)⟩

/-- Its actual integral homology class in the original small complex. -/
def positiveCircleSmallClass : CycleClass.Geometric.SmallCircleHomology.Cycles.smallCircleHomology 1 :=
  AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass CycleClass.Geometric.SmallCircleHomology.Cycles.smallCircleChains 1 positiveCircleSmallCycle

/-- The native connecting homomorphism carries the actual positive circle
to the literal oriented difference of its two overlap endpoints. -/
theorem positiveCircleSmallClass_boundary :
    CycleClass.Geometric.SmallCircleHomology.Cycles.smallCircleBoundary 0 positiveCircleSmallClass =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap) 0
        ⟨CircleArcWinding.circleOverlapDifference, AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ _⟩ :=
  AlgebraicTopology.Duality.Poincare.ConnectingRepresentatives.homologyConnecting_eq_of_lift (S)
    (CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence_shortExact CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart)
    0 positiveCircleSmallCycle positiveCircleMiddleChain
    ⟨CircleArcWinding.circleOverlapDifference, AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ _⟩ rfl positiveCircleMiddleChain_boundary

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SmallCirclePositiveCycle

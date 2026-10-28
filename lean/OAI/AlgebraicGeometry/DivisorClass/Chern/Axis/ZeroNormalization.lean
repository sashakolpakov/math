import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfChartNaturality
import OAI.AlgebraicGeometry.DivisorClass.Chern.PointCrossNormalization

/-! # Zero Normalization -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.ZeroNormalization

noncomputable section

/-!
# ChernClass: the zero-endpoint equator class is exactly the tangent sphere class

The actual overlap retraction drops the zero coordinate. The original
cross product with a point is homotopic to point inclusion, so the
remaining class is precisely the radial image of the tangent cycle.
-/

open _root_.CategoryTheory
open _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def axisZeroOverlapCycle (r n : ℕ)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
      (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1)))))) n) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OrthantBoundaryRepresentatives.orthantSphereOverlap r)) n :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (ZeroEquator.axisZeroProductOverlap r)) n
    (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (Singular.CrossBoundary.singularPointCross ℚ (TopCat.of Unit)
      (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1))))) ()) n z)

theorem axisZeroOverlapCycle_val (r n : ℕ)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
      (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1)))))) n) :
    (axisZeroOverlapCycle r n z).val = HalfChartNaturality.axisZeroOverlapChain r n z.val := rfl

theorem axisZeroOverlapCycle_lowerSphere (r n : ℕ)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
      (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1)))))) n) :
    homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
      (TopCat.ofHom (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv (r + 1)).toFun)) n
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OrthantBoundaryRepresentatives.orthantSphereOverlap r)) n (axisZeroOverlapCycle r n z)) =
      homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
        (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (r + 1)))))) n
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
          (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1)))))) n z) := by
  let Y := TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1))))
  let p := Singular.CrossBoundary.singularPointCross ℚ (TopCat.of Unit) Y ()
  let f := (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (ZeroEquator.axisZeroProductOverlap r)
  let g := (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (TopCat.ofHom (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv (r + 1)).toFun)
  let radial := (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
    (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (r + 1)))))
  have hc := AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality f n (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap p n z)
  change _ = AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OrthantBoundaryRepresentatives.orthantSphereOverlap r)) n
    (axisZeroOverlapCycle r n z) at hc
  rw [← hc, ← AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
  have hm : p ≫ f ≫ g = Singular.CrossBoundary.unitPointProjection ℚ Y ≫ radial := by
    change p ≫ ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (ZeroEquator.axisZeroProductOverlap r) ≫
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (TopCat.ofHom (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv (r + 1)).toFun)) = _
    rw [← CategoryTheory.Functor.map_comp, ZeroEquator.axisZeroProductOverlap_retraction,
      CategoryTheory.Functor.map_comp]
    exact (Category.assoc _ _ _).symm
  have hh := congrArg (fun u => homologyMap u n) hm
  rw [homologyMap_comp, homologyMap_comp, homologyMap_comp,
    PointCrossNormalization.unitPointProjection_homology, Category.id_comp] at hh
  exact ConcreteCategory.congr_hom hh (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y) n z)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.ZeroNormalization

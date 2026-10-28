import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfAmbientMaps
import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfSphereBoundary

/-! # Half Ambient Chains -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfAmbientChains

noncomputable section

/-! The actual half-interval chart chains inside the full sphere. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem axisHalfEndpointProductChain_ambient (r : ℕ) (b : Bool) (q : ℕ)
    (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin (r + 1))))).X (q + 2)) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (r + 1)) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (Half.axisProductPole (r + 1) b)))).f (q + 2)
      (HalfSphereBoundary.axisHalfEndpointProductChain r b q B) =
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (ProductEquator.axisProductRadialMap (r + 1))).f (q + 2)
        (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (HalfProductMaps.axisProductLeftPuncturedMap (r + 1))).f (q + 2)
          (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ)) (TopCat.of (EuclideanSpace ℝ (Fin (r + 1))))
            0 (q + 2) (q + 2) (by omega)
            (Singular.CrossBoundary.scalarPointChain ℚ (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ)) (Rational.AxisInterval.realAxisPuncturedPoint (fun _ => b))) B)) := by
  exact ConcreteCategory.congr_hom
    (congrArg (fun f => f.f (q + 2)) (HalfAmbientMaps.axisHalfEndpointProduct_comparison (r + 1) b)) B

theorem axisHalfRayProductChain_ambient (r : ℕ) (b : Bool) (q : ℕ)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1)))))).X (q + 1)) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (r + 1)) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (Half.axisProductPole (r + 1) b)))).f (q + 2)
      (HalfSphereBoundary.axisHalfRayProductChain r b q z) =
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (ProductEquator.axisProductRadialMap (r + 1))).f (q + 2)
        (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (HalfProductMaps.axisProductRightPuncturedMap (r + 1))).f (q + 2)
          (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of ℝ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1)))))
            1 (q + 1) (q + 2) (by omega)
            (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (HalfChains.axisHalfInclusion b)).f 1 (HalfChains.rationalAxisHalfRayChain b)) z)) := by
  let Y := TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1))))
  let H := TopCat.of (Half.axisHalfLine b)
  let f := AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((HalfChains.axisHalfInclusion b, 𝟙 Y) : (H, Y) ⟶ (TopCat.of ℝ, Y))
  let right := (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (HalfProductMaps.axisProductRightPuncturedMap (r + 1))
  let radial := (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (ProductEquator.axisProductRadialMap (r + 1))
  have hc := congrArg (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (HalfAmbientMaps.axisHalfRightChart_ambient (r + 1) b)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp] at hc
  have he := ConcreteCategory.congr_hom (congrArg (fun u => u.f (q + 2)) hc)
    (Singular.CrossBoundary.singularCrossChain ℚ H Y 1 (q + 1) (q + 2) (by omega) (HalfChains.rationalAxisHalfRayChain b) z)
  change _ = radial.f (q + 2) (right.f (q + 2) (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map f).f (q + 2) _)) at he
  have hn := Singular.CrossBoundary.singularCrossChain_naturality ℚ (HalfChains.axisHalfInclusion b) (𝟙 Y)
    1 (q + 1) (q + 2) (by omega) (HalfChains.rationalAxisHalfRayChain b) z
  rw [CategoryTheory.Functor.map_id] at hn
  exact he.trans (congrArg (fun t => radial.f (q + 2) (right.f (q + 2) t)) hn)

theorem axisHalfSphereChain_ambient_sum (r q : ℕ)
    (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin (r + 1))))).X (q + 2))
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1)))))).X (q + 1)) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (r + 1)) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (r + 1))))).f (q + 2)
          (HalfSphereBoundary.axisHalfSphereChain r false q B z) +
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (r + 1)) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (r + 1))))).f (q + 2)
          (HalfSphereBoundary.axisHalfSphereChain r true q B z) =
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (ProductEquator.axisProductRadialMap (r + 1))).f (q + 2)
        (ProductBoundary.axisProductBoundaryChain (r + 1) q B z) := by
  unfold HalfSphereBoundary.axisHalfSphereChain
  erw [map_smul, map_smul, map_sub, map_sub]
  change (-1 : ℚ) • (_ - _) + (1 : ℚ) • (_ - _) = _
  rw [neg_one_smul, one_smul]
  erw [axisHalfEndpointProductChain_ambient r false q B, axisHalfEndpointProductChain_ambient r true q B,
    axisHalfRayProductChain_ambient r false q z, axisHalfRayProductChain_ambient r true q z]
  rw [ProductBoundary.axisProductBoundaryChain, map_sub, HalfAmbientMaps.rationalAxisPuncturedEndpointChain_split,
    HalfChains.rationalAxisIntervalChain_split, Singular.CrossBoundary.singularCrossChain_sub_left, Singular.CrossBoundary.singularCrossChain_sub_left,
    map_sub, map_sub, map_sub, map_sub]
  abel

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfAmbientChains

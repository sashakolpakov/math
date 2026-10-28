import OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneHalfFillings
import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives

/-! # Plane Disk Boundary -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneDiskBoundary

noncomputable section

/-!
# ChernClass: the two supported half-disks bound the explicit positive circle

The axis chains cancel after inclusion in the coordinate plane. The
remaining arcs give exactly the previously normalized orthant circle.
-/

open _root_.CategoryTheory
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def planeHalfInclusion (b : Bool) : TopCat.of (PlaneHalf.coordinatePlaneHalf b) ⟶ TopCat.of PlaneHalf.CoordinatePlane :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def planeSphereInclusion : CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere 1 ⟶ TopCat.of PlaneHalf.CoordinatePlane :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem planeHalfAxisChain_same_ambient :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (planeHalfInclusion false)).f 1 (PlaneHalfFillings.planeHalfAxisChain false) =
      (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (planeHalfInclusion true)).f 1 (PlaneHalfFillings.planeHalfAxisChain true) := by
  rw [PlaneHalfFillings.planeHalfAxisChain, PlaneHalfFillings.planeHalfAxisChain, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro η _
  rw [map_zsmul, map_zsmul, OrthantBoundaryRepresentatives.integralSimplexChain_map, OrthantBoundaryRepresentatives.integralSimplexChain_map]
  rfl

theorem planeHalfOuterChain_ambient (b : Bool) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (planeHalfInclusion b)).f 1 (PlaneHalfFillings.planeHalfOuterChain b) =
      OrthantSphereEquator.orthantSign b • (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map planeSphereInclusion).f 1
        (∑ η : Fin 1 → Bool, OrthantSphereEquator.orthantWeight η • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ)
          (TopCat.toSSet.obj (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere 1)) (OrthantSphereEquator.orthantSphereSimplex 1 (Fin.cons b η))) := by
  rw [PlaneHalfFillings.planeHalfOuterChain, map_zsmul, map_sum, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro η _
  rw [map_zsmul, map_zsmul, OrthantBoundaryRepresentatives.integralSimplexChain_map, OrthantBoundaryRepresentatives.integralSimplexChain_map]
  rfl

theorem planeHalfOuterChain_sum_ambient :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (planeHalfInclusion false)).f 1 (PlaneHalfFillings.planeHalfOuterChain false) +
      (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (planeHalfInclusion true)).f 1 (PlaneHalfFillings.planeHalfOuterChain true) =
      (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map planeSphereInclusion).f 1 (OrthantSphereCycle.orientedOrthantSphereChain 1) := by
  rw [planeHalfOuterChain_ambient, planeHalfOuterChain_ambient, OrthantBoundaryRepresentatives.orientedOrthantSphereChain_split,
    map_add, map_neg]
  change (-1 : ℤ) • _ + (1 : ℤ) • _ = _
  rw [neg_one_zsmul, one_zsmul]

def planeDiskFilling : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of PlaneHalf.CoordinatePlane)).X 2 :=
  (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (planeHalfInclusion false)).f 2 (PlaneHalfFillings.planeHalfFilling false) +
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (planeHalfInclusion true)).f 2 (PlaneHalfFillings.planeHalfFilling true)

theorem planeHalfFilling_ambient_boundary (b : Bool) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of PlaneHalf.CoordinatePlane)).d 2 1
      ((CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (planeHalfInclusion b)).f 2 (PlaneHalfFillings.planeHalfFilling b)) =
      (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (planeHalfInclusion b)).f 1 (PlaneHalfFillings.planeHalfOuterChain b) -
        OrthantSphereEquator.orthantSign b • (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (planeHalfInclusion b)).f 1
          (PlaneHalfFillings.planeHalfAxisChain b) := by
  have h := ConcreteCategory.congr_hom
    ((CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (planeHalfInclusion b)).comm 2 1) (PlaneHalfFillings.planeHalfFilling b)
  change _ = (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (planeHalfInclusion b)).f 1
    ((CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).d 2 1 (PlaneHalfFillings.planeHalfFilling b)) at h
  rw [PlaneHalfFillings.planeHalfFilling_boundary, map_sub, map_zsmul] at h
  exact h

theorem planeDiskFilling_boundary :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of PlaneHalf.CoordinatePlane)).d 2 1 planeDiskFilling =
      (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map planeSphereInclusion).f 1 (OrthantSphereCycle.orientedOrthantSphereChain 1) := by
  rw [planeDiskFilling, map_add, planeHalfFilling_ambient_boundary,
    planeHalfFilling_ambient_boundary, planeHalfAxisChain_same_ambient]
  change (_ - (-1 : ℤ) • _) + (_ - (1 : ℤ) • _) = _
  rw [neg_one_zsmul, one_zsmul, sub_neg_eq_add]
  have h := planeHalfOuterChain_sum_ambient
  exact (show _ =
      (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (planeHalfInclusion false)).f 1 (PlaneHalfFillings.planeHalfOuterChain false) +
        (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (planeHalfInclusion true)).f 1 (PlaneHalfFillings.planeHalfOuterChain true) by abel).trans h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneDiskBoundary

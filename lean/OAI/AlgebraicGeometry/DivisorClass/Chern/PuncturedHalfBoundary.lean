import OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneProductCharts
import OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneHalfFillings
import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives

/-! # Punctured Half Boundary -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PuncturedHalfBoundary

noncomputable section

/-!
# ChernClass: the outer half-circle chain in the punctured half-plane

The outer arcs avoid the origin, including their endpoints. Their
chain in that punctured support maps to the original half-circle
chain, and its actual boundary consists of the two axis endpoints.
-/

open _root_.CategoryTheory
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def puncturedPlaneHalfInclusion (b : Bool) :
    TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b) ⟶ TopCat.of (PlaneHalf.coordinatePlaneHalf b) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem planeAxisVector_ne_zero (η : Fin 1 → Bool) : PlaneHalf.planeAxisVector η ≠ 0 := by
  intro h
  have hz := congrArg (fun x : PlaneHalf.CoordinatePlane => x 1) h
  change (OrthantSphereEquator.orthantSign (η 0) : ℝ) = 0 at hz
  exact OrthantSphereEquator.orthantSign_ne_zero (η 0) (by exact_mod_cast hz)

def planeAxisPuncturedPoint (b : Bool) (η : Fin 1 → Bool) : PlaneProductCharts.PuncturedPlaneHalf b :=
  ⟨PlaneHalf.planeAxisPoint b η, planeAxisVector_ne_zero η⟩

def planeHalfOuterPuncturedSimplex (b : Bool) (η : Fin 1 → Bool) :
    (TopCat.toSSet.obj (TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b))) _⦋1⦌ :=
  ((TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b)).toSSetObjEquiv _).symm (PlaneProductCharts.planeHalfOuterPuncturedMap b η)

theorem planeHalfOuterPuncturedSimplex_face_zero (b : Bool) (η : Fin 1 → Bool) :
    (TopCat.toSSet.obj (TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b))).δ 0 (planeHalfOuterPuncturedSimplex b η) =
      (TopCat.toSSetObj₀Equiv (X := TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b))).symm
        (planeAxisPuncturedPoint b η) := by
  apply ((TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  have h := congrArg (fun s => ((TopCat.of (PlaneHalf.coordinatePlaneHalf b)).toSSetObjEquiv _ s) t)
    (PlaneHalfFaces.planeHalfOuterSimplex_face_zero b η)
  exact h

theorem planeHalfOuterPuncturedSimplex_face_flip (b : Bool) (η : Fin 1 → Bool) (i : Fin 1) :
    (TopCat.toSSet.obj (TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b))).δ i.succ
        (planeHalfOuterPuncturedSimplex b (OrthantSphereEquator.orthantFlip i η)) =
      (TopCat.toSSet.obj (TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b))).δ i.succ
        (planeHalfOuterPuncturedSimplex b η) := by
  apply ((TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  exact congrArg (fun s => ((TopCat.of (PlaneHalf.coordinatePlaneHalf b)).toSSetObjEquiv _ s) t)
    (PlaneHalfFaces.planeHalfOuterSimplex_face_flip b η i)

def planeHalfOuterPuncturedChain (b : Bool) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b))).X 1 :=
  OrthantSphereEquator.orthantSign b • ∑ η : Fin 1 → Bool, OrthantSphereEquator.orthantWeight η • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ)
    (TopCat.toSSet.obj (TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b))) (planeHalfOuterPuncturedSimplex b η)

def planeHalfPuncturedEndpointChain (b : Bool) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b))).X 0 :=
  ∑ η : Fin 1 → Bool, OrthantSphereEquator.orthantWeight η • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ)
    (TopCat.toSSet.obj (TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b)))
    ((TopCat.toSSetObj₀Equiv (X := TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b))).symm (planeAxisPuncturedPoint b η))

theorem planeHalfOuterPuncturedChain_inclusion (b : Bool) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (puncturedPlaneHalfInclusion b)).f 1
      (planeHalfOuterPuncturedChain b) = PlaneHalfFillings.planeHalfOuterChain b := by
  rw [planeHalfOuterPuncturedChain, PlaneHalfFillings.planeHalfOuterChain, map_zsmul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro η _
  rw [map_zsmul, OrthantBoundaryRepresentatives.integralSimplexChain_map]
  rfl

theorem planeHalfOuterPuncturedChain_boundary (b : Bool) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b))).d 1 0
      (planeHalfOuterPuncturedChain b) = OrthantSphereEquator.orthantSign b • planeHalfPuncturedEndpointChain b := by
  change (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) (TopCat.toSSet.obj (TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b)))).d 1 0
    (OrthantSphereEquator.orthantSign b • ∑ η : Fin 1 → Bool, OrthantSphereEquator.orthantWeight η • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ)
      (TopCat.toSSet.obj (TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b))) (planeHalfOuterPuncturedSimplex b η)) = _
  rw [map_zsmul, OrthantWeightedBoundary.orthantWeighted_boundary_first _ 0 _ (planeHalfOuterPuncturedSimplex_face_flip b)]
  simp only [planeHalfOuterPuncturedSimplex_face_zero]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PuncturedHalfBoundary

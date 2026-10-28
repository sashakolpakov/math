import OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneHalfFaces
import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantWeightedBoundary

/-! # Plane Half Fillings -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneHalfFillings

noncomputable section

/-!
# ChernClass: actual half-plane fillings of the oriented circle

The axis rays and half-circle arcs have the same endpoint boundary.
Their signed difference is a genuine cycle in a contractible closed
half-plane, so it has an actual singular two-chain filling there.
-/

open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def planeHalfEndpointChain (b : Bool) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).X 0 :=
  ∑ η : Fin 1 → Bool, OrthantSphereEquator.orthantWeight η • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ)
    (TopCat.toSSet.obj (TopCat.of (PlaneHalf.coordinatePlaneHalf b)))
    ((TopCat.toSSetObj₀Equiv (X := TopCat.of (PlaneHalf.coordinatePlaneHalf b))).symm (PlaneHalf.planeAxisPoint b η))

def planeHalfOuterChain (b : Bool) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).X 1 :=
  OrthantSphereEquator.orthantSign b • ∑ η : Fin 1 → Bool, OrthantSphereEquator.orthantWeight η • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ)
    (TopCat.toSSet.obj (TopCat.of (PlaneHalf.coordinatePlaneHalf b))) (PlaneHalf.planeHalfOuterSimplex b η)

def planeHalfAxisChain (b : Bool) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).X 1 :=
  ∑ η : Fin 1 → Bool, OrthantSphereEquator.orthantWeight η • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ)
    (TopCat.toSSet.obj (TopCat.of (PlaneHalf.coordinatePlaneHalf b))) (PlaneHalf.planeAxisRaySimplex b η)

theorem planeHalfOuterChain_boundary (b : Bool) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).d 1 0 (planeHalfOuterChain b) =
      OrthantSphereEquator.orthantSign b • planeHalfEndpointChain b := by
  change (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) (TopCat.toSSet.obj (TopCat.of (PlaneHalf.coordinatePlaneHalf b)))).d 1 0
    (OrthantSphereEquator.orthantSign b • ∑ η : Fin 1 → Bool, OrthantSphereEquator.orthantWeight η • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ)
      (TopCat.toSSet.obj (TopCat.of (PlaneHalf.coordinatePlaneHalf b))) (PlaneHalf.planeHalfOuterSimplex b η)) = _
  rw [map_zsmul, OrthantWeightedBoundary.orthantWeighted_boundary_first _ 0 _ (PlaneHalfFaces.planeHalfOuterSimplex_face_flip b)]
  simp only [PlaneHalfFaces.planeHalfOuterSimplex_face_zero]
  rfl

theorem planeHalfAxisChain_boundary (b : Bool) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).d 1 0 (planeHalfAxisChain b) =
      planeHalfEndpointChain b := by
  have hs : ∀ η (i : Fin 1),
      (TopCat.toSSet.obj (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).δ i.succ
          (PlaneHalf.planeAxisRaySimplex b (OrthantSphereEquator.orthantFlip i η)) =
        (TopCat.toSSet.obj (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).δ i.succ (PlaneHalf.planeAxisRaySimplex b η) := by
    intro η i
    have hi : i = 0 := by omega
    subst i
    exact (PlaneHalfFaces.planeAxisRaySimplex_face_one b _).trans (PlaneHalfFaces.planeAxisRaySimplex_face_one b η).symm
  change (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) (TopCat.toSSet.obj (TopCat.of (PlaneHalf.coordinatePlaneHalf b)))).d 1 0
    (∑ η : Fin 1 → Bool, OrthantSphereEquator.orthantWeight η • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ)
      (TopCat.toSSet.obj (TopCat.of (PlaneHalf.coordinatePlaneHalf b))) (PlaneHalf.planeAxisRaySimplex b η)) = _
  rw [OrthantWeightedBoundary.orthantWeighted_boundary_first _ 0 _ hs]
  simp only [PlaneHalfFaces.planeAxisRaySimplex_face_zero]
  rfl

def planeHalfBoundaryCycle (b : Bool) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (PlaneHalf.coordinatePlaneHalf b))) 1 :=
  ⟨planeHalfOuterChain b - OrthantSphereEquator.orthantSign b • planeHalfAxisChain b, by
    rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ, map_sub, map_zsmul, planeHalfOuterChain_boundary,
      planeHalfAxisChain_boundary, sub_self]⟩

theorem exists_planeHalfFilling (b : Bool) :
    ∃ D : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).X 2,
      (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).d 2 1 D =
        planeHalfOuterChain b - OrthantSphereEquator.orthantSign b • planeHalfAxisChain b :=
  CycleClass.Geometric.SimplexFillings.Cycles.exists_singularBoundary_of_contractible (TopCat.of (PlaneHalf.coordinatePlaneHalf b)) 1 (by decide)
    (planeHalfBoundaryCycle b)

def planeHalfFilling (b : Bool) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).X 2 :=
  (exists_planeHalfFilling b).choose

theorem planeHalfFilling_boundary (b : Bool) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).d 2 1 (planeHalfFilling b) =
      planeHalfOuterChain b - OrthantSphereEquator.orthantSign b • planeHalfAxisChain b :=
  (exists_planeHalfFilling b).choose_spec

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneHalfFillings

import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneHalf
import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantSphereEquator
import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantHemisphereFaces

/-! # Plane Half Faces -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneHalfFaces

noncomputable section

/-! Actual faces of the circle arcs and axis rays in each closed half-plane. -/

open scoped Simplicial

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem oneVertexSimplex_coordinate (t : Convexity.StdSimplex ℝ (Fin 1)) : t.weights 0 = 1 := by
  have h := Convexity.StdSimplex.total_of_fintype t
  change (∑ j : Fin 1, t.weights j) = 1 at h
  simpa only [Fin.sum_univ_one] using h

theorem planeAxisRaySimplex_face_zero (b : Bool) (η : Fin 1 → Bool) :
    (TopCat.toSSet.obj (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).δ 0 (PlaneHalf.planeAxisRaySimplex b η) =
      (TopCat.toSSetObj₀Equiv (X := TopCat.of (PlaneHalf.coordinatePlaneHalf b))).symm (PlaneHalf.planeAxisPoint b η) := by
  apply ((TopCat.of (PlaneHalf.coordinatePlaneHalf b)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace 0 t).weights 1 • PlaneHalf.planeAxisVector η = PlaneHalf.planeAxisVector η
  have ht := OrthantSphereEquator.standardSimplexFace_succAbove (0 : Fin 2) t (0 : Fin 1)
  change (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace 0 t).weights 1 = t.weights 0 at ht
  rw [ht, oneVertexSimplex_coordinate, one_smul]

theorem planeAxisRaySimplex_face_one (b : Bool) (η : Fin 1 → Bool) :
    (TopCat.toSSet.obj (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).δ 1 (PlaneHalf.planeAxisRaySimplex b η) =
      (TopCat.toSSetObj₀Equiv (X := TopCat.of (PlaneHalf.coordinatePlaneHalf b))).symm (PlaneHalf.planeHalfOrigin b) := by
  apply ((TopCat.of (PlaneHalf.coordinatePlaneHalf b)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace 1 t).weights 1 • PlaneHalf.planeAxisVector η = 0
  rw [OrthantSphereEquator.standardSimplexFace_omitted_zero, zero_smul]

theorem planeHalfOuterSimplex_face_zero (b : Bool) (η : Fin 1 → Bool) :
    (TopCat.toSSet.obj (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).δ 0 (PlaneHalf.planeHalfOuterSimplex b η) =
      (TopCat.toSSetObj₀Equiv (X := TopCat.of (PlaneHalf.coordinatePlaneHalf b))).symm (PlaneHalf.planeAxisPoint b η) := by
  apply ((TopCat.of (PlaneHalf.coordinatePlaneHalf b)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change (OrthantSphereEquator.orthantSphereMap 1 (Fin.cons b η) (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace 0 t)).val = PlaneHalf.planeAxisVector η
  rw [OrthantSphereEquator.orthantSphereMap_face_zero]
  have hv : OrthantSphereEquator.orthantVector 0 η t = EuclideanSpace.single (0 : Fin 1) (OrthantSphereEquator.orthantSign (η 0) : ℝ) := by
    ext i
    have hi : i = 0 := by omega
    subst i
    change (OrthantSphereEquator.orthantSign (η 0) : ℝ) * t.weights 0 = _
    rw [oneVertexSimplex_coordinate, mul_one]
    simp
  have hn : ‖OrthantSphereEquator.orthantVector 0 η t‖ = 1 := by
    rw [hv, PiLp.norm_single, OrthantSphereEquator.orthantSign_norm]
  change ((CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates 1).symm (OrthantSphereEquator.orthantSphereMap 0 η t).val).val = _
  rw [OrthantSphereEquator.orthantSphereMap_coe, hn, inv_one, one_smul, hv]
  change (WithLp.toLp 2 (Fin.cons (α := fun _ : Fin 2 => ℝ) 0
    (fun i : Fin 1 => (EuclideanSpace.single (0 : Fin 1) (OrthantSphereEquator.orthantSign (η 0) : ℝ)) i)) :
      PlaneHalf.CoordinatePlane) = PlaneHalf.planeAxisVector η
  ext i
  fin_cases i <;> simp [PlaneHalf.planeAxisVector]

theorem planeHalfOuterSimplex_face_flip (b : Bool) (η : Fin 1 → Bool) (i : Fin 1) :
    (TopCat.toSSet.obj (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).δ i.succ
        (PlaneHalf.planeHalfOuterSimplex b (OrthantSphereEquator.orthantFlip i η)) =
      (TopCat.toSSet.obj (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).δ i.succ (PlaneHalf.planeHalfOuterSimplex b η) := by
  apply ((TopCat.of (PlaneHalf.coordinatePlaneHalf b)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change (OrthantSphereEquator.orthantSphereMap 1 (Fin.cons b (OrthantSphereEquator.orthantFlip i η)) (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace i.succ t)).val =
    (OrthantSphereEquator.orthantSphereMap 1 (Fin.cons b η) (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace i.succ t)).val
  rw [OrthantHemisphereFaces.orthantFlip_cons]
  exact congrArg Subtype.val (OrthantSphereEquator.orthantSphereMap_update_zero 1 (Fin.cons b η) i.succ
    (!(η i)) (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace i.succ t) (OrthantSphereEquator.standardSimplexFace_omitted_zero i.succ t))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneHalfFaces

import OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneProductCharts
import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantSphereEquator
import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalNormChange

/-! # Product Equator -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.ProductEquator

noncomputable section

/-!
# ChernClass: the axis product is the actual ordered sphere equator

When the plane's first coordinate vanishes, its product radial map
factors through the explicit equator inclusion. The native overlap
retraction therefore recovers exactly the radial axis-product map.
-/

open _root_.CategoryTheory OAI.AlgebraicGeometry.CycleClass.Geometric.NormalNormChange.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def axisProductLinearEquiv (m : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)) where
  toFun x := WithLp.toLp 2 (Fin.cons x.1 (fun i => x.2 i))
  invFun x := (x 0, WithLp.toLp 2 (fun i => x i.succ))
  left_inv x := by
    apply Prod.ext rfl
    ext i
    rfl
  right_inv x := by
    ext i
    exact Fin.cases rfl (fun _ => rfl) i
  map_add' x y := by
    ext i
    exact Fin.cases rfl (fun _ => rfl) i
  map_smul' a x := by
    ext i
    exact Fin.cases rfl (fun _ => rfl) i

def axisProductCoordinates (m : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin m)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
  (axisProductLinearEquiv m).toContinuousLinearEquiv

def planeAxisVectorOfReal (s : ℝ) : PlaneHalf.CoordinatePlane :=
  WithLp.toLp 2 (Fin.cons (α := fun _ : Fin 2 => ℝ) 0 (fun _ => s))

theorem planeProductCoordinates_axis (m : ℕ) (s : ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    PlaneProductCharts.planeProductCoordinates m (planeAxisVectorOfReal s, y) =
      ((CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (m + 1)).symm
        (axisProductCoordinates m (s, y))).val := by
  ext i
  refine Fin.cases rfl (fun j => ?_) i
  exact Fin.cases rfl (fun _ => rfl) j

theorem planeProductCoordinates_axis_ne_zero (m : ℕ) (s : ℝ) (y : EuclideanSpace ℝ (Fin m))
    (h : axisProductCoordinates m (s, y) ≠ 0) :
    PlaneProductCharts.planeProductCoordinates m (planeAxisVectorOfReal s, y) ≠ 0 := by
  intro hz
  apply h
  have he := planeProductCoordinates_axis m s y
  rw [hz] at he
  have hs : (CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (m + 1)).symm
      (axisProductCoordinates m (s, y)) = 0 := Subtype.ext he.symm
  exact (CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (m + 1)).symm.injective
    (hs.trans (map_zero _).symm)

theorem planeProduct_axis_radial (m : ℕ) (s : ℝ) (y : EuclideanSpace ℝ (Fin m))
    (h : axisProductCoordinates m (s, y) ≠ 0) :
    CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (m + 2)))
        ⟨PlaneProductCharts.planeProductCoordinates m (planeAxisVectorOfReal s, y), planeProductCoordinates_axis_ne_zero m s y h⟩ =
      OrthantSphereEquator.orderedEquatorSpherePoint m
        (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (m + 1)))
          ⟨axisProductCoordinates m (s, y), h⟩) := by
  apply Subtype.ext
  rw [CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection_coe]
  change ‖PlaneProductCharts.planeProductCoordinates m (planeAxisVectorOfReal s, y)‖⁻¹ •
    PlaneProductCharts.planeProductCoordinates m (planeAxisVectorOfReal s, y) = _
  rw [planeProductCoordinates_axis]
  change ‖((CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (m + 1)).symm
      (axisProductCoordinates m (s, y))).val‖⁻¹ •
        ((CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (m + 1)).symm
          (axisProductCoordinates m (s, y))).val =
    ((CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (m + 1)).symm
      (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (m + 1)))
        ⟨axisProductCoordinates m (s, y), h⟩).val).val
  rw [CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection_coe, map_smul]
  have hn : ‖((CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (m + 1)).symm
      (axisProductCoordinates m (s, y))).val‖ = ‖axisProductCoordinates m (s, y)‖ :=
    (CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (m + 1)).symm.norm_map _
  rw [hn]
  rfl

def axisProductRadialMap (m : ℕ) :
    TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (ℝ × EuclideanSpace ℝ (Fin m))) ⟶ CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere m :=
  TopCat.ofHom ((CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (m + 1)))).comp
    ⟨CycleClass.Geometric.NormalNormChange.Cycles.puncturedNormalHomeomorph (axisProductCoordinates m),
      (CycleClass.Geometric.NormalNormChange.Cycles.puncturedNormalHomeomorph (axisProductCoordinates m)).continuous⟩)

def planeAxisProductOverlap (m : ℕ) :
    TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (ℝ × EuclideanSpace ℝ (Fin m))) ⟶
      TopCat.of (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)) ∩
        CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)) : Set (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))) :=
  axisProductRadialMap m ≫ OrthantSphereEquator.orderedEquatorOverlap m

theorem planeAxisProductOverlap_retraction (m : ℕ) :
    planeAxisProductOverlap m ≫ TopCat.ofHom (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv (m + 1)).toFun =
      axisProductRadialMap m := by
  rw [planeAxisProductOverlap, Category.assoc, OrthantSphereEquator.orderedEquatorOverlap_retraction, Category.comp_id]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.ProductEquator

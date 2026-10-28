import OAI.AlgebraicGeometry.DivisorClass.Chern.PuncturedHalfSet
import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.Half

/-! # Half Product Maps -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfProductMaps

noncomputable section

/-! The shared axis product maps to the actual overlap of the two product pole charts. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def axisProductLeftPuncturedMap (m : ℕ) :
    TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ × EuclideanSpace ℝ (Fin m)) ⟶
      TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (ℝ × EuclideanSpace ℝ (Fin m))) :=
  TopCat.ofHom ⟨fun p => ⟨(p.1.val, p.2), by
      intro h
      exact p.1.property (congrArg Prod.fst h)⟩,
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _⟩

def axisProductRightPuncturedMap (m : ℕ) :
    TopCat.of (ℝ × CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))) ⟶
      TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (ℝ × EuclideanSpace ℝ (Fin m))) :=
  TopCat.ofHom ⟨fun p => ⟨(p.1, p.2.val), by
      intro h
      exact p.2.property (congrArg Prod.snd h)⟩,
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩

def axisHalfProductMap (m : ℕ) (b : Bool) :
    TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (ℝ × EuclideanSpace ℝ (Fin m))) ⟶
      TopCat.of (PuncturedHalfSet.PuncturedHalfProduct m b) :=
  TopCat.ofHom ⟨fun p => ⟨(Half.axisPlaneHalfInclusion b p.val.1, p.val.2), by
      intro h
      apply p.property
      apply Prod.ext
      · have hfirst := congrArg (fun x : PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m) => x.1 1) h
        exact hfirst
      · exact congrArg (fun x : PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m) => x.2) h⟩,
    (((Half.axisPlaneHalfInclusion b).hom.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _⟩

def planeProductOverlapToChart (m : ℕ) (b : Bool) :
    TopCat.of (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)) ∩
        CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)) : Set (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))) ⟶
      TopCat.of (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (PlaneProductCharts.planeProductPole m b)) :=
  TopCat.ofHom ⟨fun x => ⟨x.val, by
      cases b with
      | false => exact x.property.1
      | true => exact x.property.2⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem axisHalfProductMap_chart (m : ℕ) (b : Bool) :
    axisHalfProductMap m b ≫ PuncturedHalfSet.halfProductChartMap m b =
      ProductEquator.planeAxisProductOverlap m ≫ planeProductOverlapToChart m b := by
  apply TopCat.ext
  intro p
  apply Subtype.ext
  have hn : ProductEquator.axisProductCoordinates m (p.val.1, p.val.2) ≠ 0 := by
    intro h
    exact p.property ((ProductEquator.axisProductCoordinates m).injective (h.trans (map_zero _).symm))
  exact ProductEquator.planeProduct_axis_radial m p.val.1 p.val.2 hn

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfProductMaps

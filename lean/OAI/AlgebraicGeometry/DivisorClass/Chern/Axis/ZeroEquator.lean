import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.Half
import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfProductMaps
import OAI.AlgebraicTopology.Kunneth.ProductModelsAs

/-! # Zero Equator -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.ZeroEquator

noncomputable section

/-! The zero endpoint product is the actual equator in the second sphere cover. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem axisProductCoordinates_zero (r : ℕ) (y : EuclideanSpace ℝ (Fin (r + 1))) :
    ProductEquator.axisProductCoordinates (r + 1) (0, y) =
      ((CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (r + 1)).symm y).val := rfl

theorem axisZero_radial (r : ℕ) (y : CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1)))) :
    CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (r + 2)))
        ⟨ProductEquator.axisProductCoordinates (r + 1) (0, y.val), by
          intro h
          have hz : ((0 : ℝ), y.val) = 0 := (ProductEquator.axisProductCoordinates (r + 1)).injective (h.trans (map_zero _).symm)
          exact y.property (congrArg Prod.snd hz)⟩ =
      OrthantSphereEquator.orderedEquatorSpherePoint r (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (r + 1))) y) := by
  apply Subtype.ext
  rw [CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection_coe]
  change ‖ProductEquator.axisProductCoordinates (r + 1) (0, y.val)‖⁻¹ • ProductEquator.axisProductCoordinates (r + 1) (0, y.val) = _
  rw [axisProductCoordinates_zero]
  change ‖((CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (r + 1)).symm y.val).val‖⁻¹ •
    ((CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (r + 1)).symm y.val).val =
      ((CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (r + 1)).symm
        (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (r + 1))) y).val).val
  rw [CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection_coe, map_smul]
  have hn : ‖((CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (r + 1)).symm y.val).val‖ = ‖y.val‖ :=
    (CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (r + 1)).symm.norm_map _
  rw [hn]
  rfl

def axisHalfZeroPointMap (b : Bool) : TopCat.of Unit ⟶ TopCat.of (Half.axisHalfLine b) :=
  TopCat.ofHom ⟨fun _ => Half.axisHalfOrigin b, continuous_const⟩

def axisZeroProductOverlap (r : ℕ) :
    TopCat.of (Unit × CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1)))) ⟶ OrthantBoundaryRepresentatives.orthantSphereOverlap r :=
  TopCat.prodSnd (X := TopCat.of Unit) (Y := TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1))))) ≫
    TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (r + 1)))) ≫
    OrthantSphereEquator.orderedEquatorOverlap r

def axisHalfZeroProductMap (r : ℕ) (b : Bool) :
    TopCat.of (Unit × CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1)))) ⟶
      TopCat.of (Half.axisHalfLine b × CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1)))) :=
  AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((axisHalfZeroPointMap b,
    𝟙 (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1)))))) :
      (TopCat.of Unit, TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1))))) ⟶
        (TopCat.of (Half.axisHalfLine b), TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1))))))

theorem axisHalfZeroProduct_chart (r : ℕ) (b : Bool) :
    axisHalfZeroProductMap r b ≫ TopCat.ofHom (Half.axisHalfRightChartMap (r + 1) b) =
      axisZeroProductOverlap r ≫ HalfProductMaps.planeProductOverlapToChart r b := by
  apply TopCat.ext
  intro p
  apply Subtype.ext
  exact axisZero_radial r p.2

theorem axisZeroProductOverlap_retraction (r : ℕ) :
    axisZeroProductOverlap r ≫ TopCat.ofHom (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv (r + 1)).toFun =
      TopCat.prodSnd (X := TopCat.of Unit) (Y := TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1))))) ≫
        TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (r + 1)))) := by
  rw [axisZeroProductOverlap, Category.assoc, Category.assoc, OrthantSphereEquator.orderedEquatorOverlap_retraction,
    Category.comp_id]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.ZeroEquator

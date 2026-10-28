import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.RationalPointChart
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineSchemeModels

/-! # Point Chart Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PointChartCoordinates

noncomputable section

section

/-! An actual affine rational-point neighborhood gives a smooth
coordinate algebra with a constructed augmentation. The affine map
of that augmentation recovers the original point in the original family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k : Type) [Field k] (A : Over (Spec (.of k))) (p : EtaleSplittingAt.EtaleSplitting.affineOver k k ⟶ A)
    (D : RationalPointChart.AffineOverPointChart k A p)

abbrev affinePointChartAlgebra : CommAlgCat k := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k D.source

def affinePointChartIso : D.source ≅ EtaleSplittingAt.EtaleSplitting.affineOver k (affinePointChartAlgebra k A p D) :=
  HilbertConstruction.Affine.OverChartPoints.affineOverIso k D.source

def affinePointChartInclusion : EtaleSplittingAt.EtaleSplitting.affineOver k (affinePointChartAlgebra k A p D) ⟶ A :=
  (affinePointChartIso k A p D).inv ≫ D.inclusion

def affinePointChartPoint : EtaleSplittingAt.EtaleSplitting.affineOver k k ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k (affinePointChartAlgebra k A p D) :=
  D.point ≫ (affinePointChartIso k A p D).hom

def affinePointChartAugmentation : affinePointChartAlgebra k A p D →ₐ[k] k :=
  OverMorphismAlgebra.affineOverMorphismAlgebra k k (affinePointChartAlgebra k A p D) (affinePointChartPoint k A p D)

theorem affinePointChartAugmentation_fac :
    AlgebraAutomorphismNaturality.affineOverAlgHom k (affinePointChartAlgebra k A p D) k (affinePointChartAugmentation k A p D) ≫
      affinePointChartInclusion k A p D = p := by
  rw [affinePointChartAugmentation, OverMorphismAlgebra.affineOverMorphismAlgebra_recovery]
  change (D.point ≫ (affinePointChartIso k A p D).hom) ≫
    ((affinePointChartIso k A p D).inv ≫ D.inclusion) = p
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact D.commutes

instance affinePointChartInclusion_open : IsOpenImmersion (affinePointChartInclusion k A p D).left := by
  have : IsIso (affinePointChartIso k A p D).inv.left :=
    (Over.forget _).map_isIso (affinePointChartIso k A p D).inv
  have : IsOpenImmersion (affinePointChartIso k A p D).inv.left := IsOpenImmersion.of_isIso _
  exact IsOpenImmersion.comp _ _

instance affinePointChartAlgebra_smooth [Smooth A.hom] : Algebra.Smooth k (affinePointChartAlgebra k A p D) :=
  HilbertConstruction.Smooth.AffineSchemeModels.affineOverAlgebra_smooth k D.source

abbrev affinePointChartSectionAlgebra : Algebra (affinePointChartAlgebra k A p D) k :=
  (affinePointChartAugmentation k A p D).toRingHom.toAlgebra

theorem affinePointChartSection_scalarTower :
    letI := affinePointChartSectionAlgebra k A p D
    IsScalarTower k (affinePointChartAlgebra k A p D) k := by
  let := affinePointChartSectionAlgebra k A p D
  exact IsScalarTower.of_algebraMap_eq (fun r => (affinePointChartAugmentation k A p D).commutes r |>.symm)

end

/-! The actual affine neighborhood of a rational point of an integral
family is nonempty and integral, so its coordinate algebra is a domain. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k : Type) [Field k] (A : Over (Spec (.of k))) (p : EtaleSplittingAt.EtaleSplitting.affineOver k k ⟶ A)
    (D : RationalPointChart.AffineOverPointChart k A p)

instance affinePointChart_source_nonempty : Nonempty D.source.left :=
  ⟨D.point.left (IsLocalRing.closedPoint k)⟩

instance affinePointChart_source_integral [IsIntegral A.left] : IsIntegral D.source.left :=
  isIntegral_of_isOpenImmersion D.inclusion.left

instance affinePointChartAlgebra_isDomain [IsIntegral A.left] : IsDomain (affinePointChartAlgebra k A p D) :=
  inferInstanceAs (IsDomain Γ(D.source.left, ⊤))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PointChartCoordinates

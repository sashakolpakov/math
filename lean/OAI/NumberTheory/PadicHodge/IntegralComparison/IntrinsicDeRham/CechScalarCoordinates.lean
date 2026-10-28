import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechScalarProduct
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal

/-! # Cech Scalar Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechScalarCoordinates.Intrinsic

noncomputable section

/-! The cup-preserving scalar map is exactly the original native
scalar comparison on finite ordinary Čech totals and cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
  {ι : Type} [Finite ι] (U : ι → X.left.Opens)

omit [Algebra R S] [Finite ι] in
theorem coverMap : CechScalarProduct.Intrinsic.coverMap R S X Y f U =
    HomologicalComplex₂.total.map
      (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarBicomplex.BaseIntrinsicCechScalarBicomplex.inverseImageIso R S X Y f U).hom (.up ℕ) := rfl

theorem cochainMap : CechScalarProduct.Intrinsic.cochainMap R S X Y f h U =
    AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.scalarMap R S X Y f h U := by
  dsimp only [CechScalarProduct.Intrinsic.cochainMap,
    CechScalarProduct.Intrinsic.coefficientMap,
    CechCoefficient.MorphismTotalCup.cochainMap,
    GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.totalIso, Iso.trans_hom, Iso.symm_hom]
  rw [coverMap]
  dsimp only [AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.scalarMap, AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarProjection.BaseIntrinsicCechScalarProjection.map]
  simp only [HomologicalComplex₂.total.map_comp, Category.assoc]
  rfl

variable [Module.Flat R S]

theorem homologyMap (n : ℕ) : CechScalarProduct.Intrinsic.homologyMap R S X Y f h U n =
    (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.homologyMap R S X Y f h U n).hom.toAddMonoidHom.comp
      (ScalarProduct.Intrinsic.unit R S _) := by
  unfold CechScalarProduct.Intrinsic.homologyMap CoefficientCochainCup.map
  rw [cochainMap]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechScalarCoordinates.Intrinsic

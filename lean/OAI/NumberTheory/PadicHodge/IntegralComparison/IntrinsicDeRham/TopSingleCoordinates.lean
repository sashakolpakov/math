import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopSingle

/-! # Top Single Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopSingleCoordinates.Intrinsic

noncomputable section

/-! The genuine top-form single map has exactly the original
coefficient row of the native de Rham Čech bicomplex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechComplex.Intrinsic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]

abbrev module := (Affine.HomologyPresheaf.functor R X).obj (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)

theorem presheafMap_f : (TopSingle.Intrinsic.presheafMap R X g).f g =
    (singleObjXSelf (.up ℕ) g (module R X g)).hom ≫
      (CechComplex.Intrinsic.presheaves R X).map (GeometricComparison.Integral.FormsModules.IntegralFormsModules.coefficientSheafIso R X g).hom := by
  rw [TopSingle.Intrinsic.presheafMap, comp_f, singleMapHomologicalComplex_inv_app_self]
  dsimp only [Functor.mapHomologicalComplex_map_f]
  rw [TopSingle.Intrinsic.sheafMap_f, Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_assoc]
  rfl

variable {ι : Type u} (U : ι → X.left.Opens)

abbrev functor : (X.left.Opensᵒᵖ ⥤ ModuleCat.{u} R) ⥤
    CochainComplex (ModuleCat.{u} R) ℕ :=
  FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech

def sourceIso (n : ℕ) := IntegralComparison.Functor.SingleTotal.homologyIso (functor R X U) (module R X g) g n

theorem bicomplexMap_row : (TopSingle.Intrinsic.bicomplexMap R X g U).f g =
    (IntegralComparison.Functor.SingleTotal.rowIso (functor R X U) (module R X g) g).hom ≫
      (TopEdge.Intrinsic.rowIso R X U g).hom := by
  change (functor R X U).map ((TopSingle.Intrinsic.presheafMap R X g).f g) = _
  rw [presheafMap_f, Functor.map_comp]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopSingleCoordinates.Intrinsic

import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.EtaleModuleTraceComparison
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdge

/-! # Module Trace Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleTracePresheaf

noncomputable section

/-! The native de Rham transfer, conjugated by the original form
coefficient isomorphisms, is exactly the additive module-sheaf trace. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left] [IsProper Y.hom] [Smooth Y.hom]
  (q : ℕ)

def coefficientIso (Z : Over (Spec (CommRingCat.of R))) :
    (Affine.HomologyPresheaf.functor R Z).obj (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Z q) ≅
      ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Z).X q).obj :=
  (IntrinsicDeRham.CechComplex.Intrinsic.presheaves R Z).mapIso
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.coefficientSheafIso R Z q)

def transfer : (Opens.map f.left.base).op ⋙
      (Affine.HomologyPresheaf.functor R X).obj (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X q) ⟶
    (Affine.HomologyPresheaf.functor R Y).obj (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y q) :=
  Functor.whiskerLeft (Opens.map f.left.base).op (coefficientIso R q X).hom ≫
    ((FiniteEtale.DeRhamSheafTrace.trace R X Y f).f q).hom ≫
      (coefficientIso R q Y).inv

theorem forget_transfer :
    Functor.whiskerRight (transfer R X Y f q) (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) =
      ((SheafOfModules.toSheaf Y.left.ringCatSheaf).map
        (FiniteEtale.ModuleTrace.trace R X Y f q)).hom := by
  let G := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let W := (Functor.whiskeringRight Y.left.Opensᵒᵖ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj G
  change W.map (transfer R X Y f q) = _
  apply (cancel_mono (W.mapIso (coefficientIso R q Y)).hom).1
  change W.map (transfer R X Y f q) ≫ W.map (coefficientIso R q Y).hom = _
  rw [← Functor.map_comp]
  change W.map ((Functor.whiskerLeft (Opens.map f.left.base).op (coefficientIso R q X).hom ≫
    ((FiniteEtale.DeRhamSheafTrace.trace R X Y f).f q).hom ≫
      (coefficientIso R q Y).inv) ≫ (coefficientIso R q Y).hom) = _
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.map_comp]
  exact (FiniteEtale.EtaleModuleTraceComparison.comparison R X Y f q).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleTracePresheaf

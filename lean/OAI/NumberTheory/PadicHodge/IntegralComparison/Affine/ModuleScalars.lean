import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Module Scalars -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleScalars

noncomputable section

/-!
# IntegralComparison: native affine module scalars agree with the base-ring sheaf construction
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (A : Type u) [CommRing A]

def base : Over (Spec (CommRingCat.of A)) := Over.mk (𝟙 _)

theorem baseMap (U : (Spec (CommRingCat.of A)).Opens) :
    OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap A (base A) U =
      ((Spec (CommRingCat.of A)).presheaf.map U.leTop.op).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := by
  apply RingHom.ext
  intro a
  rfl

def component (M : (Spec (CommRingCat.of A)).Modules) (U : (Spec (CommRingCat.of A)).Opensᵒᵖ) :
    ((AlgebraSheafScalars.functor A (base A)).obj M).obj.obj U ≅
      (modulesSpecToSheaf.obj M).obj.obj U :=
  ModuleCat.restrictScalarsComp'App (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    ((Spec (CommRingCat.of A)).presheaf.map U.unop.leTop.op).hom
    (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap A (base A) U.unop) (baseMap A U.unop) (M.val.obj U)

def objectIso (M : (Spec (CommRingCat.of A)).Modules) :
    (AlgebraSheafScalars.functor A (base A)).obj M ≅ modulesSpecToSheaf.obj M :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (component A M)
    (by
      intro U V f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl))

def iso : AlgebraSheafScalars.functor A (base A) ≅ modulesSpecToSheaf :=
  NatIso.ofComponents (objectIso A)
    (by
      intro M N f
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleScalars

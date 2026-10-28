import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionAlgebraIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafificationRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeModuleSheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-! # Ordinary Form Open -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormOpen.OrdinaryFormOpenRestriction

noncomputable section

/-! # Ordinary structure-sheaf module forms commute with the original open restriction -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

variable (R : Type u) [CommRing R]

def moduleIso {A B : CommAlgCat.{u} R} (e : A ≅ B) (n : ℕ) :
    OrdinaryFormBase.OrdinaryFormModulePresheaf.formModule R A n ≅
      (ModuleCat.restrictScalars e.hom.hom.toRingHom).obj (OrdinaryFormBase.OrdinaryFormModulePresheaf.formModule R B n) :=
  (LinearEquiv.ofBijective (OrdinaryFormBase.OrdinaryFormModulePresheaf.formMap R e.hom n).hom
    (ConcreteCategory.bijective_of_isIso ((DeRhamGlobalId.DeRhamGlobal.formsFunctor n).map e.hom))).toModuleIso

section Presheaves

variable {C D : Type v} [Category.{w} C] [Category.{w} D]
  (F : C ⥤ D) (H : Dᵒᵖ ⥤ CommAlgCat.{u} R) (K : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  (e : K ≅ F.op ⋙ H)

def ringMap : NumberTheory.PadicHodge.IntegralComparison.AlgebraPresheafScalars.rings R K ⟶ F.op ⋙ NumberTheory.PadicHodge.IntegralComparison.AlgebraPresheafScalars.rings R H :=
  Functor.whiskerRight e.hom (forget₂ (CommAlgCat.{u} R) CommRingCat ⋙ forget₂ CommRingCat RingCat)

def presheafIso (n : ℕ) : OrdinaryFormBase.OrdinaryFormModulePresheaf.presheaf R K n ≅
    (PresheafOfModules.pushforward (ringMap R F H K e)).obj (OrdinaryFormBase.OrdinaryFormModulePresheaf.presheaf R H n) :=
  PresheafOfModules.isoMk (fun U => moduleIso R (e.app U) n) (by
    intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (DeRhamGlobalId.DeRhamGlobal.formMap_comp (K.map f) (e.hom.app V) n x).symm.trans
      ((congrArg (fun g => DeRhamGlobalId.DeRhamGlobal.formMap g n x) (e.hom.naturality f)).trans
        (DeRhamGlobalId.DeRhamGlobal.formMap_comp (e.hom.app U) (H.map (F.op.map f)) n x)))

end Presheaves

variable (X Y : Over (Spec (CommRingCat.of R))) (g : X.left ⟶ Y.left)
  [IsOpenImmersion g] (hg : g ≫ Y.hom = X.hom)

def schemeRingMap : X.left.ringCatSheaf ⟶
    (g.opensFunctor.sheafPushforwardContinuous RingCat (Opens.grothendieckTopology X.left)
      (Opens.grothendieckTopology Y.left)).obj Y.left.ringCatSheaf :=
  ⟨ringMap R g.opensFunctor (AlgebraicForms.AlgebraicDeRham.sectionAlgebras R Y)
    (AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X) (NumberTheory.PadicHodge.IntegralComparison.Open.SectionAlgebraIso.iso R X Y g hg)⟩

def iso (n : ℕ) : OrdinaryFormBase.OrdinaryFormModulePresheaf.sheaf R X n ≅
    (Scheme.Modules.restrictFunctor g).obj (OrdinaryFormBase.OrdinaryFormModulePresheaf.sheaf R Y n) :=
  (NumberTheory.PadicHodge.IntegralComparison.SchemeModuleSheafification.functor X.left).mapIso
    (presheafIso R g.opensFunctor (AlgebraicForms.AlgebraicDeRham.sectionAlgebras R Y)
      (AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X) (NumberTheory.PadicHodge.IntegralComparison.Open.SectionAlgebraIso.iso R X Y g hg) n) ≪≫
      NumberTheory.PadicHodge.IntegralComparison.Module.SheafificationRestriction.iso (schemeRingMap R X Y g hg)
        (OrdinaryFormBase.OrdinaryFormModulePresheaf.presheaf R (AlgebraicForms.AlgebraicDeRham.sectionAlgebras R Y) n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormOpen.OrdinaryFormOpenRestriction

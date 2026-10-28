import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionAlgebraIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafificationRestriction

/-! # Forms Open Restriction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsOpenRestriction.IntegralFormsOpenRestriction

noncomputable section

/-! Native integral form modules commute with actual open restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R]

def formIso {A B : CommAlgCat.{u} R} (e : A ≅ B) (n : ℕ) :
    FormsModules.IntegralFormsModules.forms R A n ≅
      (ModuleCat.restrictScalars e.hom.hom.toRingHom).obj (FormsModules.IntegralFormsModules.forms R B n) :=
  (LinearEquiv.ofBijective (FormsModules.IntegralFormsModules.map R e.hom n).hom
    (ConcreteCategory.bijective_of_isIso ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsFunctor n).map e.hom))).toModuleIso

variable (X Y : Over (Spec (CommRingCat.of R)))
  (g : X.left ⟶ Y.left) [IsOpenImmersion g] (hg : g ≫ Y.hom = X.hom)

def ringMap : X.left.ringCatSheaf ⟶
    (g.opensFunctor.sheafPushforwardContinuous RingCat (Opens.grothendieckTopology X.left)
      (Opens.grothendieckTopology Y.left)).obj Y.left.ringCatSheaf :=
  ⟨Functor.whiskerRight (IntegralComparison.Open.SectionAlgebraIso.iso R X Y g hg).hom
    (forget₂ (CommAlgCat.{u} R) CommRingCat ⋙ forget₂ CommRingCat RingCat)⟩

def presheafIso (n : ℕ) : FormsModules.IntegralFormsModules.presheaf R X n ≅
    (PresheafOfModules.pushforward (ringMap X Y g hg).hom).obj
      (FormsModules.IntegralFormsModules.presheaf R Y n) :=
  PresheafOfModules.isoMk (fun U => formIso ((IntegralComparison.Open.SectionAlgebraIso.iso R X Y g hg).app U) n)
    (by
      intro U V f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro ω
      let e := IntegralComparison.Open.SectionAlgebraIso.iso R X Y g hg
      exact (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_comp ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map f)
        (e.hom.app V) n ω).symm.trans
        ((congrArg (fun a => AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap a n ω) (e.hom.naturality f)).trans
          (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_comp (e.hom.app U)
            ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R Y).map (g.opensFunctor.op.map f)) n ω)))

def iso (n : ℕ) : FormsModules.IntegralFormsModules.sheaf R X n ≅
    (Scheme.Modules.restrictFunctor g).obj (FormsModules.IntegralFormsModules.sheaf R Y n) :=
  (IntegralComparison.SchemeModuleSheafification.functor X.left).mapIso (presheafIso X Y g hg n) ≪≫
    IntegralComparison.Module.SheafificationRestriction.iso (ringMap X Y g hg) (FormsModules.IntegralFormsModules.presheaf R Y n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsOpenRestriction.IntegralFormsOpenRestriction

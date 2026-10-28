import OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeInternalHom
import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Internal Hom -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.InternalHom

noncomputable section

/-! Sections of the genuine internal Hom on an open subscheme are
morphisms of the restricted module sheaves. The equivalence respects
precomposition, so it applies to complexes of internal Homs. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)

def overEquiv : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U) ≃+ (M.over U ⟶ N.over U) where
  toEquiv := ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction.moduleHomOverEquiv M N U
  map_add' q q' := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext m
    rfl

instance overFunctor_additive : (Scheme.Modules.overEquiv U).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

def restrictionHomEquiv : (M.over U ⟶ N.over U) ≃+
    (M.restrict U.ι ⟶ N.restrict U.ι) where
  toEquiv := (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.homEquiv.trans
    (Iso.homCongr ((Scheme.Modules.overFunctorEquiv U).app M)
      ((Scheme.Modules.overFunctorEquiv U).app N))
  map_add' f g := by
    change _ ≫ (Scheme.Modules.overEquiv U).functor.map (f + g) ≫ _ = _
    rw [(Scheme.Modules.overEquiv U).functor.map_add,
      Preadditive.add_comp, Preadditive.comp_add]
    rfl

def sectionEquiv : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U) ≃+
    (M.restrict U.ι ⟶ N.restrict U.ι) :=
  (InternalHom.overEquiv M N U).trans (restrictionHomEquiv M N U)

theorem over_precomp {M' : X.Modules} (f : M ⟶ M')
    (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M' N, U)) :
    InternalHom.overEquiv M N U ((ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality.Construction.sheafHomMap f (𝟙 N)).val.app (op U) q) =
      f.over U ≫ InternalHom.overEquiv M' N U q := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext m
  rfl

theorem restrictionHomEquiv_precomp {M' : X.Modules} (f : M ⟶ M')
    (q : M'.over U ⟶ N.over U) :
    restrictionHomEquiv M N U (f.over U ≫ q) =
      (Scheme.Modules.restrictFunctor U.ι).map f ≫ restrictionHomEquiv M' N U q := by
  change ((Scheme.Modules.overFunctorEquiv U).app M).inv ≫
    (Scheme.Modules.overEquiv U).functor.map (f.over U ≫ q) ≫
      ((Scheme.Modules.overFunctorEquiv U).app N).hom = _
  rw [CategoryTheory.Functor.map_comp]
  have h := (Scheme.Modules.overFunctorEquiv U).inv.naturality f
  change (Scheme.Modules.restrictFunctor U.ι).map f ≫
      ((Scheme.Modules.overFunctorEquiv U).app M').inv =
    ((Scheme.Modules.overFunctorEquiv U).app M).inv ≫
      (Scheme.Modules.overEquiv U).functor.map (f.over U) at h
  simp only [← Category.assoc]
  rw [← h]
  simp only [Category.assoc]
  rfl

theorem sectionEquiv_precomp {M' : X.Modules} (f : M ⟶ M')
    (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M' N, U)) :
    sectionEquiv M N U ((ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality.Construction.sheafHomMap f (𝟙 N)).val.app (op U) q) =
      (Scheme.Modules.restrictFunctor U.ι).map f ≫ sectionEquiv M' N U q := by
  change restrictionHomEquiv M N U (InternalHom.overEquiv M N U _) = _
  rw [over_precomp, restrictionHomEquiv_precomp]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.InternalHom

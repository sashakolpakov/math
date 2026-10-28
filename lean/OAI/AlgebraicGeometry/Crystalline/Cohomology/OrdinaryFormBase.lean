import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryFormScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraPresheafScalars
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Ordinary Form Base -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormBase.OrdinaryFormModulePresheaf

noncomputable section

/-! # Ordinary de Rham terms with their actual structure-ring module actions -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

variable (R : Type u) [CommRing R]

def formModule (A : CommAlgCat.{u} R) (n : ℕ) : ModuleCat.{u} A :=
  ModuleCat.of A (DeRhamPresentationTo.DeRhamPresentation.Form R A n)

def formMap {A B : CommAlgCat.{u} R} (f : A ⟶ B) (n : ℕ) :
    formModule R A n ⟶ (ModuleCat.restrictScalars f.hom.toRingHom).obj (formModule R B n) :=
  ModuleCat.ofHom (X := formModule R A n)
    (Y := (ModuleCat.restrictScalars f.hom.toRingHom).obj (formModule R B n)) {
      toFun := fun x => DeRhamGlobalId.DeRhamGlobal.formMap f n x
      map_add' := (DeRhamGlobalId.DeRhamGlobal.formMap f n).map_add
      map_smul' := NumberTheory.PadicHodge.IntegralComparison.OrdinaryFormScalars.Ordinary.formMap_smul R A B f.hom n }

def baseIso (A : CommAlgCat.{u} R) (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap R A)).obj (formModule R A n) ≅
      ModuleCat.of R (DeRhamPresentationTo.DeRhamPresentation.Form R A n) :=
  (AddEquiv.toLinearEquiv
    (M := ↑((ModuleCat.restrictScalars (algebraMap R A)).obj (formModule R A n)))
    (M₂ := ↑(ModuleCat.of R (DeRhamPresentationTo.DeRhamPresentation.Form R A n)))
    (by rfl) (fun r x => algebraMap_smul A r (show DeRhamPresentationTo.DeRhamPresentation.Form R A n from x))).toModuleIso

variable {C : Type v} [Category.{w} C] (H : Cᵒᵖ ⥤ CommAlgCat.{u} R)

def presheaf (n : ℕ) : PresheafOfModules.{u} (NumberTheory.PadicHodge.IntegralComparison.AlgebraPresheafScalars.rings R H) where
  obj U := formModule R (H.obj U) n
  map f := formMap R (H.map f) n
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change DeRhamGlobalId.DeRhamGlobal.formMap (H.map (𝟙 U)) n x = x
    rw [H.map_id]
    exact DeRhamGlobalId.DeRhamGlobal.formMap_id (H.obj U) n x
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change DeRhamGlobalId.DeRhamGlobal.formMap (H.map (f ≫ g)) n x =
      DeRhamGlobalId.DeRhamGlobal.formMap (H.map g) n (DeRhamGlobalId.DeRhamGlobal.formMap (H.map f) n x)
    rw [H.map_comp]
    exact DeRhamGlobalId.DeRhamGlobal.formMap_comp (H.map f) (H.map g) n x

def underlyingIso (n : ℕ) :
    (NumberTheory.PadicHodge.IntegralComparison.AlgebraPresheafScalars.functor R H).obj (presheaf R H n) ≅
      H ⋙ DeRhamGlobalId.DeRhamGlobal.formsFunctor n :=
  NatIso.ofComponents (fun U => baseIso R (H.obj U) n) (by
    intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

def sheaf (X : Over (Spec (CommRingCat.of R))) (n : ℕ) : X.left.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.left.ringCatSheaf.obj)).obj
    (presheaf R (AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X) n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormBase.OrdinaryFormModulePresheaf

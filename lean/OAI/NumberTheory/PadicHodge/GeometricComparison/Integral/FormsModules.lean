import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId
import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafificationScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryFormScalars

/-! # Forms Modules -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules

noncomputable section

/-! Native differential forms retain their actual structure-sheaf module structure over any base ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R]

def forms (A : CommAlgCat.{u} R) (n : ℕ) : ModuleCat.{u} A :=
  ModuleCat.of A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n)

def map {A B : CommAlgCat.{u} R} (f : A ⟶ B) (n : ℕ) :
    forms R A n ⟶ (ModuleCat.restrictScalars f.hom.toRingHom).obj (forms R B n) :=
  ModuleCat.ofHom (X := forms R A n)
    (Y := (ModuleCat.restrictScalars f.hom.toRingHom).obj (forms R B n))
    { toFun := AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n
      map_add' := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n).map_add
      map_smul' a ω := IntegralComparison.OrdinaryFormScalars.Ordinary.formMap_smul R A B f.hom n a ω }

variable {C : Type u} [Category.{u} C] (H : Cᵒᵖ ⥤ CommAlgCat.{u} R)

def formPresheaf (n : ℕ) : PresheafOfModules.{u} (IntegralComparison.AlgebraPresheafScalars.rings R H) where
  obj U := forms R (H.obj U) n
  map f := IntegralFormsModules.map R (H.map f) n
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    change AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (H.map (𝟙 U)) n ω = ω
    rw [H.map_id]
    exact AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_id _ n ω
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    change AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (H.map (f ≫ g)) n ω =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (H.map g) n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (H.map f) n ω)
    rw [H.map_comp]
    exact AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_comp _ _ n ω

variable (X : Over (Spec (CommRingCat.of R)))

def presheaf (n : ℕ) : PresheafOfModules.{u} X.left.ringCatSheaf.obj :=
  formPresheaf R (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X) n

def sheaf (n : ℕ) : X.left.Modules :=
  (IntegralComparison.SchemeModuleSheafification.functor X.left).obj (presheaf R X n)

def coefficientPresheafIso (n : ℕ) :
    (IntegralComparison.AlgebraSheafScalars.presheaves R X).obj (presheaf R X n) ≅
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n := Iso.refl _

def coefficientSheafIso (n : ℕ) : (IntegralComparison.AlgebraSheafScalars.functor R X).obj (sheaf R X n) ≅
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n :=
  (IntegralComparison.AlgebraSheafificationScalars.objectIso R X (presheaf R X n)).symm ≪≫
    (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)).mapIso
      (coefficientPresheafIso R X n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules

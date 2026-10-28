import OAI.AlgebraicGeometry.Crystalline.Cohomology.ZariskiCechIs
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SectionHypercohomologyInv
import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationSectionComplexIso

/-! # Section Unit -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.SectionUnit.CechSectionUnit

noncomputable section

/-! # The canonical sheafification unit identifies the actual Čech section complexes -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)

abbrev Sheaves := Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)

def presheafSections : Sheaves R X ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⋙
    MixedCech.Functor.MixedCechFunctor.functor R X U ⋙
      ((CategoryTheory.evaluation X.Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤)).mapHomologicalComplex (.up ℕ)

def sheafSections : Sheaves R X ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  MixedCech.Functor.MixedCechFunctor.sheafFunctor R X U ⋙
    (SectionHypercohomologyInv.SectionHypercohomology.sections R (TopCat.of X)).mapHomologicalComplex (.up ℕ)

def componentIso (F : Sheaves R X) :
    (presheafSections R X U).obj F ≅ (sheafSections R X U).obj F :=
  NumberTheory.PadicHodge.GeometricComparison.SheafificationSectionComplexIso.SheafificationSectionComplex.complexIso (Opens.grothendieckTopology X) (.up ℕ)
    ((MixedCech.Functor.MixedCechFunctor.functor R X U).obj F.obj) (op ⊤) (fun n => by
      have : IsIso (toSheafify (Opens.grothendieckTopology X)
          (((MixedCech.Functor.MixedCechFunctor.functor R X U).obj F.obj).X n)) :=
        isIso_toSheafify (Opens.grothendieckTopology X) (ZariskiCechIs.ZariskiCechPresheafSheaf.term_isSheaf R X F U n)
      infer_instance)

theorem naturality {F G : Sheaves R X} (f : F ⟶ G) :
    (presheafSections R X U).map f ≫ (componentIso R X U G).hom =
      (componentIso R X U F).hom ≫ (sheafSections R X U).map f := by
  ext n : 1
  exact congrArg (fun a => a.app (op ⊤))
    (toSheafify_naturality (Opens.grothendieckTopology X)
      (((MixedCech.Functor.MixedCechFunctor.functor R X U).map f.hom).f n))

def iso : presheafSections R X U ≅ sheafSections R X U :=
  NatIso.ofComponents (componentIso R X U) (fun {_ _} f => naturality R X U f)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.SectionUnit.CechSectionUnit

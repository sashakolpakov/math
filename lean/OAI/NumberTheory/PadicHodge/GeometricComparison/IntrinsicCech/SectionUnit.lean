import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Functor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TermsAreSheaves
import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationSectionComplexIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.Hypercohomology

/-! # Section Unit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionUnit.IntrinsicCechSectionUnit

noncomputable section

/-! On actual Čech terms of a sheaf, the canonical sheafification unit gives a natural section-complex isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] (X : Scheme.{0}) {ι : Type} (U : ι → X.Opens)

abbrev Sheaves := Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)

local notation "V" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionUnit.IntrinsicCechSectionUnit.Sheaves R X

def presheafSections : V ⥤ CochainComplex (ModuleCat.{0} R) ℕ :=
  sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R) ⋙
    Functor.IntrinsicCechFunctor.functor R X U ⋙
      ((CategoryTheory.evaluation X.Opensᵒᵖ (ModuleCat.{0} R)).obj (op ⊤)).mapHomologicalComplex (.up ℕ)

def sheafSections : V ⥤ CochainComplex (ModuleCat.{0} R) ℕ :=
  Functor.IntrinsicCechFunctor.sheafFunctor R X U ⋙
    (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X)).mapHomologicalComplex (.up ℕ)

def componentIso (F : V) : (presheafSections R X U).obj F ≅ (sheafSections R X U).obj F :=
  SheafificationSectionComplexIso.SheafificationSectionComplex.complexIso (Opens.grothendieckTopology X) (.up ℕ)
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.complex R X U F.obj) (op ⊤) (fun n => by
      have : IsIso (toSheafify (Opens.grothendieckTopology X) ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.complex R X U F.obj).X n)) :=
        Cech.TermsAreSheaves.CechTermsAreSheaves.unit_isIso R X F U n
      infer_instance)

theorem naturality {F G : V} (f : F ⟶ G) :
    (presheafSections R X U).map f ≫ (componentIso R X U G).hom =
      (componentIso R X U F).hom ≫ (sheafSections R X U).map f := by
  ext n : 1
  exact congrArg (fun a => a.app (op ⊤))
    (toSheafify_naturality (Opens.grothendieckTopology X)
      (((Functor.IntrinsicCechFunctor.functor R X U).map f.hom).f n))

def iso : presheafSections R X U ≅ sheafSections R X U :=
  NatIso.ofComponents (componentIso R X U) (fun {_ _} f => naturality R X U f)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionUnit.IntrinsicCechSectionUnit

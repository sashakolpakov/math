import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Functor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TermsAreSheaves
import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationComplex

/-! # Presheaf Unit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.PresheafUnit.IntrinsicCechPresheafUnit

noncomputable section

/-! The native Čech resolution has the original Čech presheaf complex as its underlying complex, through the actual sheafification unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)

def iso (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.complex R X U F.obj ≅
      ((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).obj
        ((Functor.IntrinsicCechFunctor.sheafFunctor R X U).obj F) := by
  let a : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.complex R X U F.obj ⟶
      ((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).obj
        ((Functor.IntrinsicCechFunctor.sheafFunctor R X U).obj F) :=
    SheafificationComplex.SheafificationComplexUnit.unit (Opens.grothendieckTopology X) (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.complex R X U F.obj)
  have (n : ℕ) : IsIso (a.f n) := Cech.TermsAreSheaves.CechTermsAreSheaves.unit_isIso R X F U n
  have ha : IsIso a := HomologicalComplex.Hom.isIso_of_components a
  exact @asIso _ _ _ _ a ha

theorem naturality {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} (a : F ⟶ G) :
    (Functor.IntrinsicCechFunctor.functor R X U).map a.hom ≫ (iso R X U G).hom =
      (iso R X U F).hom ≫
        ((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).map
          ((Functor.IntrinsicCechFunctor.sheafFunctor R X U).map a) :=
  (SheafificationComplex.SheafificationComplexUnit.naturality (Opens.grothendieckTopology X)
    ((Functor.IntrinsicCechFunctor.functor R X U).map a.hom)).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.PresheafUnit.IntrinsicCechPresheafUnit

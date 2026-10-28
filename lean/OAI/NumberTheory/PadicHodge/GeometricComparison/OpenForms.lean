import OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSectionPresheaf
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover

/-! # Open Forms -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.OpenForms.OpenFormsSheaves

noncomputable section

/-! The actual native sheafified differential forms commute with restriction along an open immersion over their base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) [IsOpenImmersion f.left]

def presheafIso (n : ℕ) :
    f.left.opensFunctor.op ⋙ AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R Y n ≅ AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (OpenSectionPresheaf.OpenSectionAlgebras.presheafIso f) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsFunctor n)

def sheafIso (n : ℕ) :
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left).obj
      ((presheafToSheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{u} R)).obj
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R Y n)) ≅
    (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n) :=
  ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafificationIso R f.left).app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R Y n)).symm ≪≫
    (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)).mapIso (presheafIso f n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.OpenForms.OpenFormsSheaves

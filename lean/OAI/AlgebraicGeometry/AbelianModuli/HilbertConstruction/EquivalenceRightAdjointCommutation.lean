import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Equivalence Right Adjoint Commutation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EquivalenceRightAdjointCommutation

noncomputable section

/-! An actual commutation isomorphism between equivalences and a left adjoint induces the corresponding commutation isomorphism for its right adjoint. -/
open _root_.CategoryTheory
universe u v w z

def rightAdjointCommutesWithEquivalences
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    {P : C ⥤ D} {R : D ⥤ C} (adj : P ⊣ R)
    (E : C ≌ C) (F : D ≌ D) (e : E.functor ⋙ P ≅ P ⋙ F.functor) :
    R ⋙ E.functor ≅ F.functor ⋙ R := by
  let d : F.inverse ⋙ R ≅ R ⋙ E.inverse :=
    conjugateIsoEquiv (adj.comp F.toAdjunction) (E.toAdjunction.comp adj) e
  exact (CategoryTheory.Functor.leftUnitor (R ⋙ E.functor)).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight F.unitIso (R ⋙ E.functor) ≪≫
    CategoryTheory.Functor.associator F.functor F.inverse (R ⋙ E.functor) ≪≫
    CategoryTheory.Functor.isoWhiskerLeft F.functor (CategoryTheory.Functor.associator F.inverse R E.functor).symm ≪≫
    CategoryTheory.Functor.isoWhiskerLeft F.functor (CategoryTheory.Functor.isoWhiskerRight d E.functor) ≪≫
    CategoryTheory.Functor.isoWhiskerLeft F.functor (CategoryTheory.Functor.associator R E.inverse E.functor) ≪≫
    CategoryTheory.Functor.isoWhiskerLeft F.functor (CategoryTheory.Functor.isoWhiskerLeft R E.counitIso) ≪≫
    CategoryTheory.Functor.isoWhiskerLeft F.functor (CategoryTheory.Functor.rightUnitor R)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EquivalenceRightAdjointCommutation

import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.Basic

/-! # Exact Homology -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology.ExactHomologyComparison

noncomputable section

/-! Homology commutes naturally with an exact coefficient functor and an actual isomorphism of complexes. -/

open _root_.CategoryTheory Limits

theorem compose {C : Type*} [Category* C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : A ⟶ F) (e : F ⟶ D)
    (f : F ⟶ G) (g : G ⟶ E) (h₁ : a ≫ b = d ≫ e) (h₂ : e ≫ c = f ≫ g) :
    a ≫ b ≫ c = (d ≫ f) ≫ g := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
  {ι : Type*} (c : ComplexShape ι)

def iso (K : HomologicalComplex C c) (L : HomologicalComplex D c)
    (e : (F.mapHomologicalComplex c).obj K ≅ L) (n : ι) : F.obj (K.homology n) ≅ L.homology n :=
  ((K.sc n).mapHomologyIso F).symm ≪≫ (HomologicalComplex.homologyFunctor D c n).mapIso e

theorem naturality {K K' : HomologicalComplex C c} {L L' : HomologicalComplex D c}
    (e : (F.mapHomologicalComplex c).obj K ≅ L)
    (e' : (F.mapHomologicalComplex c).obj K' ≅ L')
    (f : K ⟶ K') (g : L ⟶ L')
    (h : (F.mapHomologicalComplex c).map f ≫ e'.hom = e.hom ≫ g) (n : ι) :
    F.map (HomologicalComplex.homologyMap f n) ≫ (iso F c K' L' e' n).hom =
      (iso F c K L e n).hom ≫ HomologicalComplex.homologyMap g n := by
  have h₁ := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor C c n).map f) F
  have h₂ := congrArg (HomologicalComplex.homologyFunctor D c n).map h
  simp only [Functor.map_comp] at h₂
  exact compose _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology.ExactHomologyComparison

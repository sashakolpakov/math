import Mathlib.Algebra.Homology.Homotopy

/-! # Sectioned Incoming Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SectionedIncomingHomotopy

noncomputable section

/-! A homotopy of incoming-site comparisons descends through the
actual natural section isomorphism, including a change of source. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w a b c
variable {A : Type u} [Category.{a} A] [Preadditive A]
  {B : Type v} [Category.{b} B] [Preadditive B]
  {C : Type w} [Category.{c} C] [Preadditive C]
  (R : A ⥤ B) [R.Additive] (S : A ⥤ C) [S.Additive] (T : B ⥤ C) [T.Additive]
  (e : S ≅ R ⋙ T)

def map {K L : CochainComplex A ℕ}
    (f : (R.mapHomologicalComplex (.up ℕ)).obj K ⟶ (R.mapHomologicalComplex (.up ℕ)).obj L) :
    (S.mapHomologicalComplex (.up ℕ)).obj K ⟶ (S.mapHomologicalComplex (.up ℕ)).obj L :=
  ((NatIso.mapHomologicalComplex e (.up ℕ)).app K).hom ≫
    (T.mapHomologicalComplex (.up ℕ)).map f ≫
      ((NatIso.mapHomologicalComplex e (.up ℕ)).app L).inv

theorem precompose {K L J : CochainComplex A ℕ} (a : K ⟶ L)
    (f : (R.mapHomologicalComplex (.up ℕ)).obj L ⟶ (R.mapHomologicalComplex (.up ℕ)).obj J) :
    SectionedIncomingHomotopy.map R S T e ((R.mapHomologicalComplex (.up ℕ)).map a ≫ f) =
      (S.mapHomologicalComplex (.up ℕ)).map a ≫ SectionedIncomingHomotopy.map R S T e f := by
  have hn : (S.mapHomologicalComplex (.up ℕ)).map a ≫
      ((NatIso.mapHomologicalComplex e (.up ℕ)).app L).hom =
        ((NatIso.mapHomologicalComplex e (.up ℕ)).app K).hom ≫
          (T.mapHomologicalComplex (.up ℕ)).map ((R.mapHomologicalComplex (.up ℕ)).map a) :=
    (NatIso.mapHomologicalComplex e (.up ℕ)).hom.naturality a
  dsimp only [SectionedIncomingHomotopy.map]
  rw [Functor.map_comp]
  simp only [← Category.assoc]
  rw [← hn]

def homotopy {K L J : CochainComplex A ℕ} (a : K ⟶ L)
    (f : (R.mapHomologicalComplex (.up ℕ)).obj K ⟶ (R.mapHomologicalComplex (.up ℕ)).obj J)
    (g : (R.mapHomologicalComplex (.up ℕ)).obj L ⟶ (R.mapHomologicalComplex (.up ℕ)).obj J)
    (h : Homotopy f ((R.mapHomologicalComplex (.up ℕ)).map a ≫ g)) :
    Homotopy (SectionedIncomingHomotopy.map R S T e f) ((S.mapHomologicalComplex (.up ℕ)).map a ≫ SectionedIncomingHomotopy.map R S T e g) :=
  (((T.mapHomotopy h).compRight ((NatIso.mapHomologicalComplex e (.up ℕ)).app J).inv).compLeft
      ((NatIso.mapHomologicalComplex e (.up ℕ)).app K).hom).trans
    (Homotopy.ofEq (precompose R S T e a g))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SectionedIncomingHomotopy

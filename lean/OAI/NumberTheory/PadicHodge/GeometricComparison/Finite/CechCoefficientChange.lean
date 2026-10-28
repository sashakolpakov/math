import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Cech Coefficient Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange

noncomputable section

/-! Finite Čech cochains commute with any additive functor between abelian categories, including flat scalar extension. -/

open _root_.CategoryTheory Limits Opposite Simplicial _root_.AlgebraicTopology

universe u v w z a b t

variable {C : Type u} [Category.{v} C] {A : Type w} [Category.{z} A] [Abelian A]
  {B : Type a} [Category.{b} B] [Abelian B] [HasProducts.{t} A] [HasProducts.{t} B]
  (G : A ⥤ B) [G.Additive] (E : SimplicialObject (FormalCoproduct.{t} C))
  (hE : ∀ n : SimplexCategory, Finite (E.obj (op n)).I)

def cosimplicialIso (P : Cᵒᵖ ⥤ A) :
    (FormalCoproduct.cosimplicialObjectFunctor E).obj P ⋙ G ≅
      (FormalCoproduct.cosimplicialObjectFunctor E).obj (P ⋙ G) :=
  NatIso.ofComponents (fun n => by
    have : Finite (E.obj (op n)).I := hE n
    exact PreservesProduct.iso G (fun i : (E.obj (op n)).I => P.obj (op ((E.obj (op n)).obj i))))
    (by
      intro n m f
      let En := E.obj (op n)
      let Em := E.obj (op m)
      let φ : Em ⟶ En := E.map f.op
      exact AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.piComparison_natural G (fun i : En.I => P.obj (op (En.obj i)))
        (fun i : Em.I => P.obj (op (Em.obj i))) φ.f (fun i => P.map (φ.φ i).op))

def complexIso (P : Cᵒᵖ ⥤ A) :
    (G.mapHomologicalComplex (.up ℕ)).obj ((FormalCoproduct.cochainComplexFunctor E).obj P) ≅
      (FormalCoproduct.cochainComplexFunctor E).obj (P ⋙ G) :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.mapCofaceIso G ((FormalCoproduct.cosimplicialObjectFunctor E).obj P) ≪≫
    (alternatingCofaceMapComplex B).mapIso (cosimplicialIso G E hE P)

theorem hom_f (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (complexIso G E hE P).hom.f n =
      piComparison G (fun i : (E.obj (op ⦋n⦌)).I => P.obj (op ((E.obj (op ⦋n⦌)).obj i))) :=
  Category.id_comp _

theorem naturality {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (G.mapHomologicalComplex (.up ℕ)).map ((FormalCoproduct.cochainComplexFunctor E).map f) ≫
      (complexIso G E hE Q).hom =
    (complexIso G E hE P).hom ≫
      (FormalCoproduct.cochainComplexFunctor E).map (Functor.whiskerRight f G) := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, hom_f]
  exact AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.piComparison_map G
    (fun i : (E.obj (op ⦋n⦌)).I => f.app (op ((E.obj (op ⦋n⦌)).obj i)))

def iso : FormalCoproduct.cochainComplexFunctor E ⋙ G.mapHomologicalComplex (.up ℕ) ≅
    (Functor.whiskeringRight Cᵒᵖ A B).obj G ⋙ FormalCoproduct.cochainComplexFunctor E :=
  NatIso.ofComponents (complexIso G E hE) (fun {_ _} f => naturality G E hE f)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange

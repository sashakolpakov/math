import OAI.AlgebraicGeometry.Comparison.Betti.FormalCechFunctor
import OAI.AlgebraicGeometry.Comparison.Betti.CofaceFunctor
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-! # Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Cech.Functor

noncomputable section

/-! Additive product-preserving functors commute naturally with the actual Čech complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

variable {C A B : Type*} [Category* C] [Category* A] [Category* B]
  [HasProducts.{0} A] [HasProducts.{0} B] [Preadditive A] [Preadditive B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{0, 0} G]

def formalCosimplicialCompIso (E : SimplicialObject (FormalCoproduct.{0} C)) (P : Cᵒᵖ ⥤ A) :
    ((FormalCoproduct.cosimplicialObjectFunctor E).obj P) ⋙ G ≅
      (FormalCoproduct.cosimplicialObjectFunctor E).obj (P ⋙ G) :=
  Functor.associator E.rightOp ((FormalCoproduct.evalOp C A).obj P) G ≪≫
    Functor.isoWhiskerLeft E.rightOp (FormalCechFunctor.formalEvalCompIso G P)

def formalCechCompIso (E : SimplicialObject (FormalCoproduct.{0} C)) (P : Cᵒᵖ ⥤ A) :
    (G.mapHomologicalComplex (.up ℕ)).obj ((FormalCoproduct.cochainComplexFunctor E).obj P) ≅
      (FormalCoproduct.cochainComplexFunctor E).obj (P ⋙ G) :=
  CofaceFunctor.Cech.cofaceFunctorIso G ((FormalCoproduct.cosimplicialObjectFunctor E).obj P) ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex B).mapIso (formalCosimplicialCompIso G E P)

theorem formalCechCompIso_hom_f
    (E : SimplicialObject (FormalCoproduct.{0} C)) (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (formalCechCompIso G E P).hom.f n =
      (FormalCechFunctor.formalEvalCompIso G P).hom.app (E.rightOp.obj ⦋n⦌) := by
  change 𝟙 _ ≫ (𝟙 _ ≫ (FormalCechFunctor.formalEvalCompIso G P).hom.app (E.rightOp.obj ⦋n⦌)) = _
  simp only [Category.id_comp]

theorem formalCechCompIso_naturality (E : SimplicialObject (FormalCoproduct.{0} C))
    {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (G.mapHomologicalComplex (.up ℕ)).map ((FormalCoproduct.cochainComplexFunctor E).map f) ≫
        (formalCechCompIso G E Q).hom =
      (formalCechCompIso G E P).hom ≫
        (FormalCoproduct.cochainComplexFunctor E).map (Functor.whiskerRight f G) := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, formalCechCompIso_hom_f]
  exact FormalCechFunctor.formalEvalCompIso_naturality G f (E.rightOp.obj ⦋n⦌)

def cechComplexFunctorComparison [HasFiniteProducts C] {ι : Type} (U : ι → C) :
    cechComplexFunctor U ⋙ G.mapHomologicalComplex (.up ℕ) ≅
      (Functor.whiskeringRight Cᵒᵖ A B).obj G ⋙ cechComplexFunctor U :=
  NatIso.ofComponents (fun P => formalCechCompIso G (FormalCoproduct.mk _ U).cech P)
    (fun f => formalCechCompIso_naturality G (FormalCoproduct.mk _ U).cech f)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Cech.Functor

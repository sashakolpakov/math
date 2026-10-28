import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Formal Cech Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FormalCechFunctor

noncomputable section

/-! Product-preserving functors commute with the actual formal Čech evaluation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

variable {C A B : Type*} [Category* C] [Category* A] [Category* B]
  [HasProducts.{0} A] [HasProducts.{0} B]
  (G : A ⥤ B) [PreservesLimitsOfSize.{0, 0} G] (P : Cᵒᵖ ⥤ A)

def formalEvalCompIso :
    (FormalCoproduct.evalOp.{0} C A).obj P ⋙ G ≅
      (FormalCoproduct.evalOp.{0} C B).obj (P ⋙ G) :=
  NatIso.ofComponents
    (fun Q => PreservesProduct.iso G (fun i : Q.unop.I => P.obj (op (Q.unop.obj i))))
    (fun {Q R} f => by
      apply Pi.hom_ext
      intro i
      change (G.map (Pi.lift (fun j : R.unop.I =>
          Pi.π (fun k : Q.unop.I => P.obj (op (Q.unop.obj k))) (f.unop.f j) ≫
            P.map (f.unop.φ j).op)) ≫
          (PreservesProduct.iso G (fun j : R.unop.I => P.obj (op (R.unop.obj j)))).hom) ≫
          Pi.π _ i =
        ((PreservesProduct.iso G (fun j : Q.unop.I => P.obj (op (Q.unop.obj j)))).hom ≫
          Pi.lift (fun j : R.unop.I =>
            Pi.π (fun k : Q.unop.I => G.obj (P.obj (op (Q.unop.obj k)))) (f.unop.f j) ≫
              G.map (P.map (f.unop.φ j).op))) ≫
          Pi.π (fun j : R.unop.I => G.obj (P.obj (op (R.unop.obj j)))) i
      simp only [PreservesProduct.iso_hom, Category.assoc, piComparison_comp_π,
        ← G.map_comp, Pi.lift_comp_π]
      rw [G.map_comp, ← Category.assoc, piComparison_comp_π])

theorem formalEvalCompIso_naturality {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q)
    (T : (FormalCoproduct.{0} C)ᵒᵖ) :
    G.map (((FormalCoproduct.evalOp C A).map f).app T) ≫ (formalEvalCompIso G Q).hom.app T =
      (formalEvalCompIso G P).hom.app T ≫
        ((FormalCoproduct.evalOp C B).map (Functor.whiskerRight f G)).app T := by
  change G.map (Limits.Pi.map (fun i : T.unop.I => f.app (op (T.unop.obj i)))) ≫
      piComparison G (fun i : T.unop.I => Q.obj (op (T.unop.obj i))) =
    piComparison G (fun i : T.unop.I => P.obj (op (T.unop.obj i))) ≫
      Limits.Pi.map (fun i : T.unop.I => G.map (f.app (op (T.unop.obj i))))
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, piComparison_comp_π, ← G.map_comp, Pi.map_π, G.map_comp,
    Category.assoc, Pi.map_π, ← Category.assoc, piComparison_comp_π]

end

end OAI.AlgebraicGeometry.Comparison.Betti.FormalCechFunctor

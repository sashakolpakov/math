import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafEvaluation
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Sheaf Transpose -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality

noncomputable section

/-!
# CartierDuality: transposition and the self-adjunction of the actual Cartier character functor
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

namespace SheafTranspose.Construction.SelfDuality

variable {C : Type u} [Category.{v} C] (D : Cᵒᵖ ⥤ C)
    (β : ∀ X : C, X ⟶ D.obj (Opposite.op (D.obj (Opposite.op X))))
    (hn : ∀ {X Y : C} (f : X ⟶ Y),
      β X ≫ D.map (D.map f.op).op = f ≫ β Y)
    (ht : ∀ X : C, β (D.obj (Opposite.op X)) ≫ D.map (β X).op = 𝟙 (D.obj (Opposite.op X)))

/-- Natural evaluation satisfying the triangle identity makes a
contravariant dual functor adjoint to its opposite. -/
def adjunction : D.rightOp ⊣ D where
  unit :=
    { app X := β X
      naturality := fun X Y f => (hn f).symm }
  counit :=
    { app X := (β X.unop).op
      naturality := by
        intro X Y f
        apply Quiver.Hom.unop_inj
        exact hn f.unop }
  left_triangle_components X := by
    apply Quiver.Hom.unop_inj
    exact ht X
  right_triangle_components X := ht X.unop

/-- Transposition of a map into a character object. -/
def transpose {X Y : C} (a : X ⟶ D.obj (Opposite.op Y)) : Y ⟶ D.obj (Opposite.op X) :=
  β Y ≫ D.map a.op

include hn ht in
/-- Transposing twice recovers the original map, without requiring
the evaluation maps to be isomorphisms. -/
theorem transpose_transpose {X Y : C} (a : X ⟶ D.obj (Opposite.op Y)) :
    transpose D β (transpose D β a) = a := by
  change β X ≫ D.map (β Y ≫ D.map a.op).op = a
  rw [op_comp, D.map_comp, ← Category.assoc, hn a, Category.assoc, ht Y, Category.comp_id]

/-- The two descriptions of a pairing as an adjoint map are equivalent. -/
def transposeEquiv (X Y : C) :
    (X ⟶ D.obj (Opposite.op Y)) ≃ (Y ⟶ D.obj (Opposite.op X)) where
  toFun := transpose D β
  invFun := transpose D β
  left_inv := transpose_transpose D β hn ht
  right_inv := transpose_transpose D β hn ht

end SheafTranspose.Construction.SelfDuality

/-- The actual Cartier character functor is a right adjoint, with
its opposite as left adjoint, on all commutative fppf sheaves. -/
def SheafTranspose.Construction.Schemes.cartierSheafAdjunction (S : Scheme.{u}) :
    (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).rightOp ⊣ CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S :=
  SheafTranspose.Construction.SelfDuality.adjunction (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S) SheafEvaluation.Construction.Schemes.sheafBidualEvaluation
    (fun a => SheafEvaluation.Construction.Schemes.sheafBidualEvaluation_natural a) SheafEvaluation.Construction.Schemes.sheafBidualEvaluation_triangle

/-- Transposition is an equivalence between the two adjoint
descriptions of a bilinear pairing of commutative fppf sheaves. -/
def SheafTranspose.Construction.Schemes.sheafPairingTransposeEquiv {S : Scheme.{u}} (G H : CommutativeSheavesAb.Construction.Schemes.FppfAb S) :
    (G ⟶ CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf H) ≃ (H ⟶ CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G) :=
  SheafTranspose.Construction.SelfDuality.transposeEquiv (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S) SheafEvaluation.Construction.Schemes.sheafBidualEvaluation
    (fun a => SheafEvaluation.Construction.Schemes.sheafBidualEvaluation_natural a) SheafEvaluation.Construction.Schemes.sheafBidualEvaluation_triangle G H

/-- Flipping a pairing transposes its actual adjoint map. -/
def SheafEvaluation.Construction.Schemes.BilinearPairing.flip {S : Scheme.{u}} {G H : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (e : SheafEvaluation.Construction.Schemes.BilinearPairing G H) :
    SheafEvaluation.Construction.Schemes.BilinearPairing H G := ⟨e.rightAdjoint⟩

/-- Flipping twice leaves the original bilinear pairing unchanged. -/
theorem SheafEvaluation.Construction.Schemes.BilinearPairing.flip_flip {S : Scheme.{u}} {G H : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (e : SheafEvaluation.Construction.Schemes.BilinearPairing G H) :
    e.flip.flip = e := by
  cases e with
  | mk a =>
    apply congrArg SheafEvaluation.Construction.Schemes.BilinearPairing.mk
    exact (SheafTranspose.Construction.Schemes.sheafPairingTransposeEquiv G H).symm_apply_apply a

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality

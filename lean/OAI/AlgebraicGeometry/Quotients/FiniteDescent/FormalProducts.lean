import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Formal Products -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.FormalProducts

noncomputable section

/-! Evaluation on formal coproducts commutes with a product-preserving functor. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w

namespace Construction.FormalProductsFunctor

variable {C : Type u} [Category.{u} C]
variable {V : Type v} [Category.{u} V] [HasProducts.{u} V]
variable {W : Type w} [Category.{u} W] [HasProducts.{u} W]
variable (F : V ⥤ W) [PreservesLimitsOfSize.{u, u} F]

omit [PreservesLimitsOfSize.{u, u} F] in
theorem pi_naturality {I J : Type u} (P : I → V) (Q : J → V)
    (f : J → I) (φ : ∀ j, P (f j) ⟶ Q j) :
    F.map (Pi.lift (fun j => Pi.π P (f j) ≫ φ j)) ≫ piComparison F Q =
      piComparison F P ≫ Pi.lift (fun j => Pi.π (fun i => F.obj (P i)) (f j) ≫ F.map (φ j)) := by
  apply Pi.hom_ext
  intro j
  simp only [Category.assoc, piComparison_comp_π, Pi.lift_comp_π, ← F.map_comp]
  rw [piComparison_comp_π_assoc, ← F.map_comp]

def evalIso (P : Cᵒᵖ ⥤ V) :
    (FormalCoproduct.evalOp.{u} C V).obj P ⋙ F ≅
      (FormalCoproduct.evalOp.{u} C W).obj (P ⋙ F) :=
  NatIso.ofComponents (fun A : (FormalCoproduct.{u} C)ᵒᵖ => asIso (piComparison F (fun i : A.unop.I => P.obj (op (A.unop.obj i)))))
    (by
      intro A B f
      exact pi_naturality F (fun i : A.unop.I => P.obj (op (A.unop.obj i)))
        (fun i : B.unop.I => P.obj (op (B.unop.obj i))) f.unop.f
        (fun i => P.map (f.unop.φ i).op))

theorem hom_π (P : Cᵒᵖ ⥤ V) (A : (FormalCoproduct.{u} C)ᵒᵖ) (i : A.unop.I) :
    (evalIso F P).hom.app A ≫
        Pi.π (fun j : A.unop.I => F.obj (P.obj (op (A.unop.obj j)))) i =
      F.map (Pi.π (fun j : A.unop.I => P.obj (op (A.unop.obj j))) i) :=
  piComparison_comp_π F _ i

end Construction.FormalProductsFunctor

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.FormalProducts

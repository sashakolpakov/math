import Mathlib.CategoryTheory.Category.Basic

/-! # Projection Transport -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Cech.ProjectionTransport

/-! Compose a Čech projection formula with a second factorwise transport. -/

open _root_.CategoryTheory

universe u v

theorem comp_projection_transport {C : Type u} [Category.{v} C]
    {A B D E F G : C} (f : A ⟶ B) (e : B ⟶ D) (p : D ⟶ E)
    (q : B ⟶ F) (r : F ⟶ E) (s : A ⟶ G) (u : G ⟶ F)
    (he : e ≫ p = q ≫ r) (hf : f ≫ q = s ≫ u) :
    (f ≫ e) ≫ p = s ≫ u ≫ r :=
  (Category.assoc _ _ _).trans ((congrArg (f ≫ ·) he).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ r) hf).trans (Category.assoc _ _ _))))

end OAI.AlgebraicGeometry.Comparison.Betti.Cech.ProjectionTransport

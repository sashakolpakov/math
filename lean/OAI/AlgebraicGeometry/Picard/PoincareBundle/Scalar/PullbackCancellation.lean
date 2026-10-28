import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Pullback Cancellation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.PullbackCancellation

/-! Cancellation of the two-sided pullback uses scalar epimorphisms on the source. -/

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {A B D E : C} [GrpObj B] [GrpObj D]
  (f : A ⟶ B) [Epi f] (g : D ⟶ E) (r : E ⟶ D) (n : ℕ)
  (hg : g ≫ r = (𝟙 D) ^ n) [Epi ((𝟙 B) ^ n)]

include hg

/-- A scalar complementary map makes two-sided pullback injective on actual group homomorphisms. -/
theorem pullback_injective (a b : B ⟶ D) [IsMonHom a] [IsMonHom b]
    (h : f ≫ a ≫ g = f ≫ b ≫ g) : a = b := by
  have hh : a ≫ g = b ≫ g := (cancel_epi f).mp h
  have hn := congrArg (fun k => k ≫ r) hh
  rw [Category.assoc, Category.assoc, hg, MonObj.comp_pow, MonObj.comp_pow,
    Category.comp_id, Category.comp_id] at hn
  apply (cancel_epi ((𝟙 B) ^ n)).mp
  simpa only [MonObj.pow_comp, Category.id_comp] using hn

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.PullbackCancellation

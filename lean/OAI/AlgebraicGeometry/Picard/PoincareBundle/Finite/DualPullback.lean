import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FiniteImages

/-! # Dual Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.DualPullback

/-! Finiteness descends from the actual two-sided pullback through a surjective quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem finite_of_finite_pullback {S : Scheme.{u}} {A B D E : Over S}
    (f : A ⟶ B) (m : B ⟶ D) (g : D ⟶ E)
    [Surjective f.left] [IsProper B.hom] [IsSeparated D.hom]
    [IsFinite (f ≫ m ≫ g).left] : IsFinite m.left := by
  have hs : IsSeparated (g.left ≫ E.hom) := by rw [Over.w]; infer_instance
  have : IsSeparated g.left := IsSeparated.of_comp g.left E.hom
  have hf : IsFinite ((f.left ≫ m.left) ≫ g.left) := by
    rw [Category.assoc]
    exact inferInstanceAs (IsFinite (f ≫ m ≫ g).left)
  have : IsFinite (f.left ≫ m.left) := IsFinite.of_comp (f.left ≫ m.left) g.left
  have hp : IsProper (m.left ≫ D.hom) := by rw [Over.w]; infer_instance
  have : IsProper m.left := IsProper.of_comp m.left D.hom
  exact AbelianScheme.CartierDuality.FiniteImages.Construction.Schemes.finite_of_proper_of_surjective_comp f.left m.left

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.DualPullback

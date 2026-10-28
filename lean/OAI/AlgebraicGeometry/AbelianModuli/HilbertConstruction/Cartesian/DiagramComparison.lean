import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Diagram Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.DiagramComparison

noncomputable section

/-! Pullback pasting identifies arrow squares and the recovery of a diagram pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C]

theorem isPullback_arrow_of_base_squares
    {A B A₀ B₀ S S₀ : C} (qA : A ⟶ A₀) (qB : B ⟶ B₀)
    (a : A ⟶ S) (b : B ⟶ S) (a₀ : A₀ ⟶ S₀) (b₀ : B₀ ⟶ S₀) (c : S ⟶ S₀)
    (f : A ⟶ B) (f₀ : A₀ ⟶ B₀)
    (hA : IsPullback qA a a₀ c) (hB : IsPullback qB b b₀ c)
    (hf : f ≫ b = a) (hf₀ : f₀ ≫ b₀ = a₀) (hq : qA ≫ f₀ = f ≫ qB) :
    IsPullback qA f f₀ qB := by
  have h : IsPullback qA (f ≫ b) (f₀ ≫ b₀) c := by
    rw [hf, hf₀]
    exact hA
  exact h.of_bot hq hB

theorem isPullback_comparison_recovery
    {P A B Z A₀ B₀ Z₀ S S₀ : C}
    (i : P ⟶ A) (j : P ⟶ B) (f : A ⟶ Z) (g : B ⟶ Z)
    (qA : A ⟶ A₀) (qB : B ⟶ B₀) (qZ : Z ⟶ Z₀)
    (f₀ : A₀ ⟶ Z₀) (g₀ : B₀ ⟶ Z₀) [HasPullback f₀ g₀]
    (b : B ⟶ S) (b₀ : B₀ ⟶ S₀) (c : S ⟶ S₀)
    (hP : IsPullback i j f g) (hA : IsPullback qA f f₀ qZ)
    (hB : IsPullback qB b b₀ c) (hg : g ≫ qZ = qB ≫ g₀)
    (r : P ⟶ pullback f₀ g₀)
    (hr₁ : r ≫ pullback.fst f₀ g₀ = i ≫ qA)
    (hr₂ : r ≫ pullback.snd f₀ g₀ = j ≫ qB) :
    IsPullback r (j ≫ b) (pullback.snd f₀ g₀ ≫ b₀) c := by
  have h : IsPullback (r ≫ pullback.fst f₀ g₀) j f₀ (qB ≫ g₀) := by
    rw [hr₁, ← hg]
    exact hP.paste_horiz hA
  exact (h.of_right hr₂ (IsPullback.of_hasPullback f₀ g₀)).paste_vert hB

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.DiagramComparison

import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Monomorphism Pullback Criterion -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.MonomorphismPullbackCriterion.Construction

noncomputable section

/-! A commuting square of monomorphisms is Cartesian when every
compatible test point admits a lift along one projection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

theorem monoSquare_isPullback {C : Type u} [Category.{v} C] {X Y Z S : C}
    (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ S) (k : Z ⟶ S) [Mono g] [Mono h]
    (hw : f ≫ h = g ≫ k)
    (hl : ∀ (T : C) (y : T ⟶ Y) (z : T ⟶ Z), y ≫ h = z ≫ k →
      ∃ x : T ⟶ X, x ≫ g = z) : IsPullback f g h k := by
  apply IsPullback.of_map yoneda hw
  apply IsPullback.of_forall_isPullback_app
  intro T
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro x
    change (x ≫ f) ≫ h = (x ≫ g) ≫ k
    simp only [Category.assoc, hw]
  · intro x x' hx
    exact (cancel_mono g).mp hx.2
  · intro y z hyz
    obtain ⟨x, hx⟩ := hl T.unop y z hyz
    refine ⟨x, ?_, hx⟩
    apply (cancel_mono h).mp
    change (x ≫ f) ≫ h = y ≫ h
    rw [Category.assoc, hw, ← Category.assoc, hx]
    exact hyz.symm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.MonomorphismPullbackCriterion.Construction

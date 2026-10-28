import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! # Ext Vanishing -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ExtVanishing

noncomputable section

/-! Actual Ext vanishing gives dimension shifting and lifting of ordinary morphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (A : C) {S : ShortComplex C} (hS : S.ShortExact)

include hS

theorem right_ext_subsingleton (q : ℕ)
    [Subsingleton (Ext A S.X₂ q)] [Subsingleton (Ext A S.X₁ (q + 1))] :
    Subsingleton (Ext A S.X₃ q) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ A hS x rfl (Subsingleton.elim _ _)
  rw [Subsingleton.elim y 0, Ext.zero_comp] at hy
  exact hy.symm

theorem hom_lift_of_ext_one [Subsingleton (Ext A S.X₁ 1)] (f : A ⟶ S.X₃) :
    ∃ g : A ⟶ S.X₂, g ≫ S.g = f := by
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ A hS (Ext.mk₀ f)
    (n₁ := 1) rfl (Subsingleton.elim _ _)
  refine ⟨Ext.homEquiv₀ y, ?_⟩
  apply (Ext.mk₀_bijective A S.X₃).injective
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
  exact hy

end

end OAI.AlgebraicGeometry.Comparison.Betti.ExtVanishing

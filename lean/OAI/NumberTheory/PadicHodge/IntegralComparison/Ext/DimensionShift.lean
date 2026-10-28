import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-! # Dimension Shift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift

noncomputable section

/-!
# IntegralComparison: dimension shifting through actual short exact sequences
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v z

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (X : C) {S : ShortComplex C} (hS : S.ShortExact) (m : ℕ)

abbrev connecting : Ext.{z} X S.X₃ m →+ Ext.{z} X S.X₁ (m + 1) :=
  hS.extClass.postcomp X rfl

theorem connecting_injective [Subsingleton (Ext.{z} X S.X₂ m)] :
    Function.Injective (connecting X hS m) := by
  apply (AddMonoidHom.ker_eq_bot_iff (connecting X hS m)).mp
  rw [AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ X hS x rfl hx
  exact hy.symm.trans (by rw [Subsingleton.elim y 0, Ext.zero_comp])

theorem connecting_surjective [Subsingleton (Ext.{z} X S.X₂ (m + 1))] :
    Function.Surjective (connecting X hS m) := by
  intro x
  exact Ext.covariant_sequence_exact₁ X hS x (Subsingleton.elim _ _) rfl

def equivalence [Subsingleton (Ext.{z} X S.X₂ m)] [Subsingleton (Ext.{z} X S.X₂ (m + 1))] :
    Ext.{z} X S.X₃ m ≃+ Ext.{z} X S.X₁ (m + 1) :=
  AddEquiv.ofBijective (connecting X hS m) ⟨connecting_injective X hS m, connecting_surjective X hS m⟩

def linearEquivalence (R : Type*) [CommRing R] [Linear R C]
    [Subsingleton (Ext.{z} X S.X₂ m)] [Subsingleton (Ext.{z} X S.X₂ (m + 1))] :
    Ext.{z} X S.X₃ m ≃ₗ[R] Ext.{z} X S.X₁ (m + 1) :=
  LinearEquiv.ofBijective (hS.extClass.postcompOfLinear R X rfl)
    ⟨connecting_injective X hS m, connecting_surjective X hS m⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift

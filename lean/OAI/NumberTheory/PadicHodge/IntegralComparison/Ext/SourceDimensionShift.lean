import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-! # Source Dimension Shift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceDimensionShift

noncomputable section

/-! Dimension shifting in the first argument of the actual original Ext groups. -/

open _root_.CategoryTheory

open Abelian

universe u v z

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {S : ShortComplex C} (hS : S.ShortExact) (Y : C) (m : ℕ)

abbrev connecting : Ext.{z} S.X₁ Y m →+ Ext.{z} S.X₃ Y (m + 1) :=
  hS.extClass.precomp Y (Nat.add_comm 1 m)

theorem connecting_injective [Subsingleton (Ext.{z} S.X₂ Y m)] :
    Function.Injective (connecting hS Y m) := by
  apply (AddMonoidHom.ker_eq_bot_iff (connecting hS Y m)).mp
  rw [AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hS Y x (Nat.add_comm 1 m) hx
  exact hy.symm.trans (by rw [Subsingleton.elim y 0, Ext.comp_zero])

theorem connecting_surjective [Subsingleton (Ext.{z} S.X₂ Y (m + 1))] :
    Function.Surjective (connecting hS Y m) := by
  intro x
  exact Ext.contravariant_sequence_exact₃ hS Y x (Subsingleton.elim _ _) (Nat.add_comm 1 m)

def linearEquivalence (R : Type*) [CommRing R] [Linear R C]
    [Subsingleton (Ext.{z} S.X₂ Y m)] [Subsingleton (Ext.{z} S.X₂ Y (m + 1))] :
    Ext.{z} S.X₁ Y m ≃ₗ[R] Ext.{z} S.X₃ Y (m + 1) :=
  LinearEquiv.ofBijective (hS.extClass.precompOfLinear R Y (Nat.add_comm 1 m))
    ⟨connecting_injective hS Y m, connecting_surjective hS Y m⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceDimensionShift

import Mathlib

/-! # Ext Isomorphism -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.ExtIsomorphism

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Abelian

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The actual contravariant transport on Ext along an isomorphism of its source. -/
def sourceEquiv {A A' : C} (e : A ≅ A') (B : C) (n : ℕ) :
    Ext A B n ≃+ Ext A' B n where
  toFun a := (Ext.mk₀ e.inv).comp a (Nat.zero_add n)
  invFun a := (Ext.mk₀ e.hom).comp a (Nat.zero_add n)
  left_inv a := by simp
  right_inv a := by simp
  map_add' a b := by simp

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.ExtIsomorphism

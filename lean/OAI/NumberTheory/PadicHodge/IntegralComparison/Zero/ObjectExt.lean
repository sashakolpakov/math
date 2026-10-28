import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-! # Object Ext -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.ObjectExt

/-! Original Ext groups vanish when either actual argument is a zero object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (X Y : C) (n : ℕ)

theorem target (hY : IsZero Y) : Subsingleton (Abelian.Ext X Y n) := by
  apply subsingleton_of_forall_eq 0
  intro x
  have h : (𝟙 Y) = 0 := hY.eq_of_src _ _
  rw [← Abelian.Ext.comp_mk₀_id x, h, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]

theorem source (hX : IsZero X) : Subsingleton (Abelian.Ext X Y n) := by
  apply subsingleton_of_forall_eq 0
  intro x
  have h : (𝟙 X) = 0 := hX.eq_of_src _ _
  rw [← Abelian.Ext.mk₀_id_comp x, h, Abelian.Ext.mk₀_zero, Abelian.Ext.zero_comp]

end OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.ObjectExt

import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroCokernel

/-! # Connecting Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ConnectingNaturality

noncomputable section

/-!
# IntegralComparison: the original Ext connecting maps are natural for actual short exact sequences
-/

open _root_.CategoryTheory

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C)
  {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)

theorem connecting (m : ℕ) (α : Ext.{z} X S.X₃ m) :
    DimensionShift.connecting X hT m ((Ext.mk₀ φ.τ₃).postcomp X (add_zero m) α) =
      (Ext.mk₀ φ.τ₁).postcomp X (add_zero (m + 1)) (DimensionShift.connecting X hS m α) := by
  change (α.comp (Ext.mk₀ φ.τ₃) (add_zero m)).comp hT.extClass rfl =
    (α.comp hS.extClass rfl).comp (Ext.mk₀ φ.τ₁) (add_zero (m + 1))
  rw [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero, hS.extClass_naturality hT φ]

theorem zero : (ModuleFunctor.functor R X 0).map φ.τ₃ ≫ ZeroCokernel.connecting R X hT =
    ZeroCokernel.connecting R X hS ≫ (ModuleFunctor.functor R X 1).map φ.τ₁ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  exact connecting X hS hT φ 0 α

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ConnectingNaturality

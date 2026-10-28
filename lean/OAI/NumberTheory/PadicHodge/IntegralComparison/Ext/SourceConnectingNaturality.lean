import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceZeroCokernel

/-! # Source Connecting Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceConnectingNaturality

noncomputable section

/-! The original source Ext connecting maps are natural for short exact sequence maps. -/

open _root_.CategoryTheory

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (Y : C)
  {S T : ShortComplex Cᵒᵖ} (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)

theorem connecting (m : ℕ) (α : Ext.{z} S.X₃.unop Y m) :
    SourceDimensionShift.connecting hT.unop Y m ((Ext.mk₀ φ.τ₃.unop).precomp Y (zero_add m) α) =
      (Ext.mk₀ φ.τ₁.unop).precomp Y (zero_add (m + 1)) (SourceDimensionShift.connecting hS.unop Y m α) := by
  change hT.unop.extClass.comp ((Ext.mk₀ φ.τ₃.unop).comp α (zero_add m)) (Nat.add_comm 1 m) =
    (Ext.mk₀ φ.τ₁.unop).comp (hS.unop.extClass.comp α (Nat.add_comm 1 m)) (zero_add (m + 1))
  refine (Ext.comp_assoc_of_second_deg_zero _ _ _ (Nat.add_comm 1 m)).symm.trans ?_
  refine (congrArg (fun e => e.comp α (Nat.add_comm 1 m))
    (hT.unop.extClass_naturality hS.unop (ShortComplex.unopMap φ))).trans ?_
  exact Ext.comp_assoc _ _ _ (zero_add 1) (Nat.add_comm 1 m) (by omega)

theorem zero : (ContravariantModuleFunctor.functor R Y 0).map φ.τ₃ ≫
    SourceZeroCokernel.connecting R Y hT = SourceZeroCokernel.connecting R Y hS ≫
      (ContravariantModuleFunctor.functor R Y 1).map φ.τ₁ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  exact connecting Y hS hT φ 0 α

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceConnectingNaturality

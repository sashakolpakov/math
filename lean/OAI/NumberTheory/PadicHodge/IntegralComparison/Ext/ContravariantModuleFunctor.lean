import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor

/-! # Contravariant Module Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ContravariantModuleFunctor

noncomputable section

/-! The original Ext groups, with their coefficient modules, are contravariant in their first argument. -/

open _root_.CategoryTheory Opposite

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (Y : C) (n : ℕ)

def functor : Cᵒᵖ ⥤ ModuleCat.{z} R where
  obj X := ModuleCat.of R (Ext.{z} X.unop Y n)
  map f := ModuleCat.ofHom ((Ext.mk₀ f.unop).precompOfLinear R Y (zero_add n))
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    exact Ext.mk₀_id_comp α
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    exact (Ext.mk₀_comp_mk₀_assoc g.unop f.unop α).symm

instance additive : (functor R Y n).Additive where
  map_add {X X'} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    change Ext.{z} X.unop Y n at α
    change (Ext.mk₀ (f.unop + g.unop)).comp α (zero_add n) =
      (Ext.mk₀ f.unop).comp α (zero_add n) + (Ext.mk₀ g.unop).comp α (zero_add n)
    rw [Ext.mk₀_add, Ext.add_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ContravariantModuleFunctor

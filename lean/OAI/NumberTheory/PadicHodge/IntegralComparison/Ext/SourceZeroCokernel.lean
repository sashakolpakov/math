import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceDimensionShift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ContravariantModuleFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Source Zero Cokernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceZeroCokernel

noncomputable section

/-! The original contravariant Ext connecting map computes the degree-zero cokernel. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (Y : C)
  {S : ShortComplex Cᵒᵖ} (hS : S.ShortExact)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y 0

def connecting : (F).obj S.X₃ ⟶ ModuleCat.of R (Ext.{z} S.X₁.unop Y 1) :=
  ModuleCat.ofHom (hS.unop.extClass.precompOfLinear R Y rfl)

theorem condition : (F).map S.g ≫ connecting R Y hS = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  change Ext.{z} S.X₂.unop Y 0 at α
  change hS.unop.extClass.comp ((Ext.mk₀ S.g.unop).comp α (zero_add 0)) rfl = 0
  exact ShortComplex.ShortExact.extClass_comp_assoc hS.unop α

def sequence : ShortComplex (ModuleCat.{z} R) :=
  ShortComplex.mk ((F).map S.g) (connecting R Y hS) (condition R Y hS)

theorem sequence_exact : (sequence R Y hS).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro α hα
  exact Ext.contravariant_sequence_exact₁ hS.unop Y α rfl hα

theorem connecting_epi [Subsingleton (Ext.{z} S.X₂.unop Y 1)] : Epi (connecting R Y hS) := by
  let : Subsingleton (Ext.{z} S.unop.X₂ Y (0 + 1)) :=
    inferInstanceAs (Subsingleton (Ext.{z} S.X₂.unop Y 1))
  exact (ModuleCat.epi_iff_surjective _).mpr (SourceDimensionShift.connecting_surjective hS.unop Y 0)

def isCokernel [Subsingleton (Ext.{z} S.X₂.unop Y 1)] :
    IsColimit (CokernelCofork.ofπ (connecting R Y hS) (condition R Y hS)) := by
  let : Epi (sequence R Y hS).g := connecting_epi R Y hS
  exact (sequence_exact R Y hS).gIsCokernel

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceZeroCokernel

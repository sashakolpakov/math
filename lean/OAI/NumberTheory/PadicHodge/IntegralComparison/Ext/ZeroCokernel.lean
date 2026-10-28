import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Zero Cokernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroCokernel

noncomputable section

/-!
# IntegralComparison: the connecting map identifies the actual degree-zero Ext cokernel
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C)
  {S : ShortComplex C} (hS : S.ShortExact)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0

def connecting : (F).obj S.X₃ ⟶ ModuleCat.of R (Ext.{z} X S.X₁ 1) :=
  ModuleCat.ofHom (hS.extClass.postcompOfLinear R X rfl)

theorem condition : (F).map S.g ≫ connecting R X hS = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  change Ext.{z} X S.X₂ 0 at α
  change (α.comp (Ext.mk₀ S.g) (add_zero 0)).comp hS.extClass rfl = 0
  simp only [Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

def sequence : ShortComplex (ModuleCat.{z} R) :=
  ShortComplex.mk ((F).map S.g) (connecting R X hS) (condition R X hS)

theorem sequence_exact : (sequence R X hS).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro α hα
  exact Ext.covariant_sequence_exact₃ X hS α rfl hα

theorem connecting_epi [Subsingleton (Ext.{z} X S.X₂ 1)] : Epi (connecting R X hS) :=
  (ModuleCat.epi_iff_surjective _).mpr (DimensionShift.connecting_surjective X hS 0)

def isCokernel [Subsingleton (Ext.{z} X S.X₂ 1)] :
    IsColimit (CokernelCofork.ofπ (connecting R X hS) (condition R X hS)) := by
  let : Epi (sequence R X hS).g := connecting_epi R X hS
  exact (sequence_exact R X hS).gIsCokernel

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroCokernel

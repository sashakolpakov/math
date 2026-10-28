import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceExactFunctorModule
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.Resolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycleMaps

/-! # Exact Functor Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorComplex

noncomputable section

/-! The native exact-functor Ext maps form a map of the actual resolution section complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

attribute [local instance] preservesFiniteLimits_op preservesFiniteColimits_op

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (Y : C)
  (K : CochainComplex Cᵒᵖ ℕ)

local notation "L" => Functor.obj (Functor.mapHomologicalComplex F.op (ComplexShape.up ℕ)) K

def map : Resolution.Comparison.complex R Y K ⟶
    Resolution.Comparison.complex R (F.obj Y) L where
  f i := Ext.SourceExactFunctorModule.component F R Y 0 (K.X i)
  comm' i j _ := (Ext.SourceExactFunctorModule.naturality F R Y 0 (K.d i j)).symm

theorem differential (n : ℕ) : Augmented.ResolutionCycleMaps.differential (map F R Y K) n =
    Ext.SourceExactFunctorModule.shortMap F R Y 0 (Augmented.ResolutionCycles.differentialSequence K n) := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorComplex

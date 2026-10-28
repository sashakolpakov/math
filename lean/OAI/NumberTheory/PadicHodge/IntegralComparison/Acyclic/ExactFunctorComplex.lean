import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ExactFunctorModule
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycleMaps

/-! # Exact Functor Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ExactFunctorComplex

noncomputable section

/-! The native exact-functor Ext maps form a map of the actual resolution section complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (X : C)
  (K : CochainComplex C ℕ)

local notation "L" => Functor.obj (Functor.mapHomologicalComplex F (ComplexShape.up ℕ)) K

def map : Resolution.Comparison.complex R X K ⟶
    Resolution.Comparison.complex R (F.obj X) L where
  f i := Ext.ExactFunctorModule.component F R X 0 (K.X i)
  comm' i j _ := (Ext.ExactFunctorModule.naturality F R X 0 (K.d i j)).symm

theorem differential (n : ℕ) : Augmented.ResolutionCycleMaps.differential (map F R X K) n =
    Ext.ExactFunctorModule.shortMap F R X 0 (Augmented.ResolutionCycles.differentialSequence K n) := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ExactFunctorComplex

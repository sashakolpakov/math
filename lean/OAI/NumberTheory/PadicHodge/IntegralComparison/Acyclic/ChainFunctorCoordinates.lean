import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainFunctorNaturality

/-! # Chain Functor Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainFunctorCoordinates

noncomputable section

/-! The actual source-resolution cochain map acts on degree-zero Ext by restriction and precomposition. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (Y : C)
  (P : ChainComplex C ℕ) (Q : ChainComplex D ℕ)
  (β : Q ⟶ (F.mapHomologicalComplex (.down ℕ)).obj P)

theorem map_mk (a : ℕ) (f : P.X a ⟶ Y) :
    (ChainFunctorNaturality.map F R Y P Q β).f a (Ext.mk₀ f) = Ext.mk₀ (β.f a ≫ F.map f) := by
  change (Ext.mk₀ (β.f a)).comp ((Ext.mk₀ f).mapExactFunctor F) (zero_add 0) = _
  rw [Ext.mapExactFunctor_mk₀]
  exact Ext.mk₀_comp_mk₀ _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainFunctorCoordinates

import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ContravariantModuleFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Source Exact Functor Module -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceExactFunctorModule

noncomputable section

/-! Exact functors act naturally on the original contravariant coefficient-module-valued Ext functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (Y : C) (n : ℕ)

def component (X : Cᵒᵖ) : (ContravariantModuleFunctor.functor R Y n).obj X ⟶
    (ContravariantModuleFunctor.functor R (F.obj Y) n).obj (F.op.obj X) :=
  ModuleCat.ofHom (F.mapExtLinearMap R X.unop Y n)

theorem naturality {X Z : Cᵒᵖ} (f : X ⟶ Z) :
    (ContravariantModuleFunctor.functor R Y n).map f ≫ component F R Y n Z =
      component F R Y n X ≫ (ContravariantModuleFunctor.functor R (F.obj Y) n).map (F.op.map f) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  change ((Ext.mk₀ f.unop).comp α (zero_add n)).mapExactFunctor F =
    (Ext.mk₀ (F.map f.unop)).comp (α.mapExactFunctor F) (zero_add n)
  exact (Ext.mapExactFunctor_comp F (Ext.mk₀ f.unop) α (zero_add n)).trans
    (congrArg (fun e : Ext.{z} (F.obj Z.unop) (F.obj X.unop) 0 =>
      e.comp (α.mapExactFunctor F) (zero_add n)) (Ext.mapExactFunctor_mk₀ F f.unop))

def transformation : ContravariantModuleFunctor.functor R Y n ⟶
    F.op ⋙ ContravariantModuleFunctor.functor R (F.obj Y) n where
  app := component F R Y n
  naturality _ _ f := SourceExactFunctorModule.naturality F R Y n f

def shortMap (T : ShortComplex Cᵒᵖ) : T.map (ContravariantModuleFunctor.functor R Y n) ⟶
    (T.map F.op).map (ContravariantModuleFunctor.functor R (F.obj Y) n) where
  τ₁ := component F R Y n T.X₁
  τ₂ := component F R Y n T.X₂
  τ₃ := component F R Y n T.X₃
  comm₁₂ := (SourceExactFunctorModule.naturality F R Y n T.f).symm
  comm₂₃ := (SourceExactFunctorModule.naturality F R Y n T.g).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceExactFunctorModule

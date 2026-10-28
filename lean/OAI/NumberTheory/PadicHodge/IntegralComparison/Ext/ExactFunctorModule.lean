import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Exact Functor Module -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ExactFunctorModule

noncomputable section

/-! Exact functors act naturally on the original coefficient-module-valued Ext functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (X : C) (n : ℕ)

def component (Y : C) : (ModuleFunctor.functor R X n).obj Y ⟶
    (ModuleFunctor.functor R (F.obj X) n).obj (F.obj Y) :=
  ModuleCat.ofHom (F.mapExtLinearMap R X Y n)

theorem naturality {Y Z : C} (f : Y ⟶ Z) :
    (ModuleFunctor.functor R X n).map f ≫ component F R X n Z =
      component F R X n Y ≫ (ModuleFunctor.functor R (F.obj X) n).map (F.map f) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  change (α.comp (Ext.mk₀ f) (add_zero n)).mapExactFunctor F =
    (α.mapExactFunctor F).comp (Ext.mk₀ (F.map f)) (add_zero n)
  exact (Ext.mapExactFunctor_comp F α (Ext.mk₀ f) (add_zero n)).trans
    (congrArg (fun e : Ext.{z} (F.obj Y) (F.obj Z) 0 =>
      (α.mapExactFunctor F).comp e (add_zero n)) (Ext.mapExactFunctor_mk₀ F f))

def transformation : ModuleFunctor.functor R X n ⟶
    F ⋙ ModuleFunctor.functor R (F.obj X) n where
  app := component F R X n
  naturality _ _ f := ExactFunctorModule.naturality F R X n f

def shortMap (T : ShortComplex C) : T.map (ModuleFunctor.functor R X n) ⟶
    (T.map F).map (ModuleFunctor.functor R (F.obj X) n) where
  τ₁ := component F R X n T.X₁
  τ₂ := component F R X n T.X₂
  τ₃ := component F R X n T.X₃
  comm₁₂ := (ExactFunctorModule.naturality F R X n T.f).symm
  comm₂₃ := (ExactFunctorModule.naturality F R X n T.g).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ExactFunctorModule

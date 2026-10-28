import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Module Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor

noncomputable section

/-!
# IntegralComparison: the original Ext groups as a coefficient-module-valued functor
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C) (n : ℕ)

def functor : C ⥤ ModuleCat.{z} R where
  obj Y := ModuleCat.of R (Ext.{z} X Y n)
  map f := ModuleCat.ofHom ((Ext.mk₀ f).postcompOfLinear R X (add_zero n))
  map_id Y := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    exact congrArg (fun g : AddCommGrpCat.of (Ext.{z} X Y n) ⟶ AddCommGrpCat.of (Ext.{z} X Y n) => g α)
      ((extFunctorObj X n).map_id Y)
  map_comp {Y Z T} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    exact congrArg (fun h : AddCommGrpCat.of (Ext.{z} X Y n) ⟶ AddCommGrpCat.of (Ext.{z} X T n) => h α)
      ((extFunctorObj X n).map_comp f g)

instance additive : (functor R X n).Additive where
  map_add {Y Z} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    exact congrArg (fun h : AddCommGrpCat.of (Ext.{z} X Y n) ⟶ AddCommGrpCat.of (Ext.{z} X Z n) => h α)
      ((extFunctorObj X n).map_add (f := f) (g := g))

def forgetIso : functor R X n ⋙ forget₂ (ModuleCat.{z} R) AddCommGrpCat ≅ extFunctorObj X n :=
  NatIso.ofComponents (fun Y => (AddEquiv.refl (Ext.{z} X Y n)).toAddCommGrpIso) (by
    intro Y Z f
    apply AddCommGrpCat.hom_ext
    ext α
    rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor

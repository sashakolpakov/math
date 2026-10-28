import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ContravariantModuleFunctor
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Ulift

/-! # Zero Contravariant Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroContravariantSections

noncomputable section

/-! Original degree-zero Ext agrees naturally with the coefficient-linear contravariant Hom functor. -/

open _root_.CategoryTheory Opposite

universe u v w z

variable {C : Type u} [Category.{v} C] [Abelian C]
  (R : Type w) [CommRing R] [Linear R C] [HasExt.{max v z} C] (Y : C)

def equivalence (X : C) : Abelian.Ext.{max v z} X Y 0 ≃ₗ[R] ULift.{z} (X ⟶ Y) :=
  Abelian.Ext.linearEquiv₀.trans ULift.moduleEquiv.symm

theorem equivalence_mk (X : C) (a : X ⟶ Y) :
    equivalence R Y X (Abelian.Ext.mk₀ a) = ULift.up a :=
  congrArg ULift.up (Abelian.Ext.linearEquiv₀.apply_symm_apply a)

def iso : ContravariantModuleFunctor.functor R Y 0 ≅
    (linearYoneda R C).obj Y ⋙ ModuleCat.uliftFunctor.{z, v} R :=
  NatIso.ofComponents (fun X => (equivalence R Y X.unop).toModuleIso) (by
    intro X X' b
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := (Abelian.Ext.mk₀_bijective X.unop Y).2 x
    have h := (congrArg (equivalence R Y X'.unop) (Abelian.Ext.mk₀_comp_mk₀ b.unop a)).trans
      (equivalence_mk R Y X'.unop (b.unop ≫ a))
    exact h.trans (congrArg (fun y : ULift.{z} (X.unop ⟶ Y) => ULift.up (b.unop ≫ y.down))
      (equivalence_mk R Y X.unop a)).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroContravariantSections

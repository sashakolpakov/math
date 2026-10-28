import OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveSectionNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafLinear
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Ulift

/-! # Zero Presheaf Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections

noncomputable section

/-!
# IntegralComparison: degree-zero Ext sections agree naturally with presheaf sections
-/

open _root_.CategoryTheory

universe u v w z

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]

abbrev constantUnit : Sheaf J (ModuleCat.{w} R) :=
  (constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R)

def homLinearEquiv (M : Sheaf J (ModuleCat.{w} R)) :
    (constantUnit R J ⟶ M) ≃ₗ[R] ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R) ⟶ M.obj) :=
  LinearAdjunction.homLinearEquiv R (sheafificationAdjunction J (ModuleCat.{w} R))
    ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R)) M

theorem homLinearEquiv_natural {M N : Sheaf J (ModuleCat.{w} R)}
    (a : constantUnit R J ⟶ M) (b : M ⟶ N) :
    homLinearEquiv R J N (a ≫ b) = homLinearEquiv R J M a ≫ b.hom :=
  (sheafificationAdjunction J (ModuleCat.{w} R)).homEquiv_naturality_right a b

variable [HasExt.{max u w z} (Sheaf J (ModuleCat.{w} R))]

def equivalence (M : Sheaf J (ModuleCat.{w} R)) :
    Abelian.Ext.{max u w z} (constantUnit R J) M 0 ≃ₗ[R]
      ULift.{z} ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R) ⟶ M.obj) :=
  Abelian.Ext.linearEquiv₀.trans ((homLinearEquiv R J M).trans ULift.moduleEquiv.symm)

theorem equivalence_mk (M : Sheaf J (ModuleCat.{w} R)) (a : constantUnit R J ⟶ M) :
    equivalence R J M (Abelian.Ext.mk₀ a) = ULift.up (homLinearEquiv R J M a) :=
  congrArg (fun b => ULift.up (homLinearEquiv R J M b)) (Abelian.Ext.linearEquiv₀.apply_symm_apply a)

def iso : ModuleFunctor.functor R (constantUnit R J) 0 ≅
    sheafToPresheaf J (ModuleCat.{w} R) ⋙
      ExhaustiveSectionNaturality.globalSectionsFunctor R (ModuleCat.of R R) ⋙
        ModuleCat.uliftFunctor.{z, max u w} R :=
  NatIso.ofComponents (fun M => (equivalence R J M).toModuleIso) (by
    intro M N b
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := (Abelian.Ext.mk₀_bijective (constantUnit R J) M).2 x
    have h := (congrArg (equivalence R J N) (Abelian.Ext.mk₀_comp_mk₀ a b)).trans
      ((equivalence_mk R J N (a ≫ b)).trans (congrArg ULift.up (homLinearEquiv_natural R J a b)))
    exact h.trans (congrArg
      (fun y : ULift.{z} ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R) ⟶ M.obj) => ULift.up (y.down ≫ b.hom))
      (equivalence_mk R J M a).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections

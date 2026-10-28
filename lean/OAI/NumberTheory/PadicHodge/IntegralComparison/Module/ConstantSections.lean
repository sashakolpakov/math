import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafLinear
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Constant Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ConstantSections

noncomputable section

/-!
# IntegralComparison: elements of constant coefficient modules give actual degree-zero Ext sections
-/

open _root_.CategoryTheory

open Abelian

universe u v w z

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]

def elementHom (M : ModuleCat.{w} R) : M ≃ₗ[R] (ModuleCat.of R R ⟶ M) :=
  (LinearMap.ringLmapEquivSelf R R M).symm.trans
    (ModuleCat.homLinearEquiv (R := R) (S := R) (M := ModuleCat.of R R) (N := M)).symm

theorem elementHom_natural {M N : ModuleCat.{w} R} (g : M ⟶ N) (m : M) :
    elementHom R M m ≫ g = elementHom R N (g m) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change g (r • m) = r • g m
  exact g.hom.map_smul r m

abbrev constantUnit : Sheaf J (ModuleCat.{w} R) :=
  (constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R)

variable [HasExt.{z} (Sheaf J (ModuleCat.{w} R))]

def globalElement (M : ModuleCat.{w} R) : M →ₗ[R]
    Ext.{z} (constantUnit R J) ((constantSheaf J (ModuleCat.{w} R)).obj M) 0 :=
  (Ext.linearEquiv₀ (R := R) (X := constantUnit R J)
    (Y := (constantSheaf J (ModuleCat.{w} R)).obj M)).symm.toLinearMap.comp
    (((constantSheaf J (ModuleCat.{w} R)).mapLinearMap R).comp (elementHom R M).toLinearMap)

theorem globalElement_apply (M : ModuleCat.{w} R) (m : M) :
    globalElement R J M m = Ext.mk₀ ((constantSheaf J (ModuleCat.{w} R)).map (elementHom R M m)) := rfl

theorem globalElement_natural {M N : ModuleCat.{w} R} (g : M ⟶ N) (m : M) :
    (IntegralComparison.Ext.ModuleFunctor.functor R (constantUnit R J) 0).map
      ((constantSheaf J (ModuleCat.{w} R)).map g) (globalElement R J M m) =
        globalElement R J N (g m) := by
  change (Ext.mk₀ ((constantSheaf J (ModuleCat.{w} R)).map (elementHom R M m))).comp
    (Ext.mk₀ ((constantSheaf J (ModuleCat.{w} R)).map g)) (add_zero 0) =
      Ext.mk₀ ((constantSheaf J (ModuleCat.{w} R)).map (elementHom R N (g m)))
  rw [Ext.mk₀_comp_mk₀, ← Functor.map_comp, elementHom_natural]

def sectionMap (M : ModuleCat.{w} R) (N : Sheaf J (ModuleCat.{w} R))
    (α : (constantSheaf J (ModuleCat.{w} R)).obj M ⟶ N) : M →ₗ[R] Ext.{z} (constantUnit R J) N 0 :=
  ((IntegralComparison.Ext.ModuleFunctor.functor R (constantUnit R J) 0).map α).hom.comp (globalElement R J M)

theorem section_apply (M : ModuleCat.{w} R) (N : Sheaf J (ModuleCat.{w} R))
    (α : (constantSheaf J (ModuleCat.{w} R)).obj M ⟶ N) (m : M) :
    sectionMap R J M N α m = Ext.mk₀ ((constantSheaf J (ModuleCat.{w} R)).map (elementHom R M m) ≫ α) :=
  Ext.mk₀_comp_mk₀ _ _

theorem section_natural {M M' : ModuleCat.{w} R} {N N' : Sheaf J (ModuleCat.{w} R)}
    (g : M ⟶ M') (h : N ⟶ N')
    (α : (constantSheaf J (ModuleCat.{w} R)).obj M ⟶ N)
    (α' : (constantSheaf J (ModuleCat.{w} R)).obj M' ⟶ N')
    (hc : (constantSheaf J (ModuleCat.{w} R)).map g ≫ α' = α ≫ h) (m : M) :
    (IntegralComparison.Ext.ModuleFunctor.functor R (constantUnit R J) 0).map h (sectionMap R J M N α m) =
      sectionMap R J M' N' α' (g m) := by
  change (sectionMap R J M N α m).comp (Ext.mk₀ h) (add_zero 0) = _
  rw [section_apply, Ext.mk₀_comp_mk₀, section_apply]
  apply congrArg (fun a : constantUnit R J ⟶ N' => (Ext.mk₀ a : Ext.{z} (constantUnit R J) N' 0))
  rw [Category.assoc, ← hc, ← Category.assoc, ← Functor.map_comp, elementHom_natural]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ConstantSections

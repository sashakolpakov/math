import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafLinear
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafResolutionSections

/-! # Sheaf Linear Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafLinearSections

noncomputable section

/-!
# IntegralComparison: coefficient-linear sections at a terminal object
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe w z u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type w) [CommRing R] [HasSheafify J (ModuleCat.{w} R)]
  {T : C} (hT : IsTerminal T)

instance evaluation_linear : ((sheafSections J (ModuleCat.{w} R)).obj (op T)).Linear R where
  map_smul := by intros; rfl

abbrev constantUnit : Sheaf J (ModuleCat.{w} R) :=
  (constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R)

def homLinearEquiv (M : Sheaf J (ModuleCat.{w} R)) :
    (constantUnit J R ⟶ M) ≃ₗ[R] M.obj.obj (op T) :=
  (LinearAdjunction.homLinearEquiv R (constantSheafAdj J (ModuleCat.{w} R) hT)
    (ModuleCat.of R R) M).trans
      ((ModuleCat.homLinearEquiv (R := R) (S := R) (M := ModuleCat.of R R)
        (N := M.obj.obj (op T))).trans (LinearMap.ringLmapEquivSelf R R _))

theorem homLinearEquiv_apply (M : Sheaf J (ModuleCat.{w} R)) (a : constantUnit J R ⟶ M) :
    SheafLinearSections.homLinearEquiv J R hT M a = SheafResolutionSections.homEquiv J R hT M a := rfl

theorem homLinearEquiv_natural {M N : Sheaf J (ModuleCat.{w} R)}
    (a : constantUnit J R ⟶ M) (b : M ⟶ N) :
    SheafLinearSections.homLinearEquiv J R hT N (a ≫ b) = b.hom.app (op T) (SheafLinearSections.homLinearEquiv J R hT M a) :=
  SheafResolutionSections.homEquiv_natural J R hT a b

variable [HasExt.{z} (Sheaf J (ModuleCat.{w} R))]

def degreeZeroLinearEquiv (M : Sheaf J (ModuleCat.{w} R)) :
    Abelian.Ext.{z} (constantUnit J R) M 0 ≃ₗ[R] M.obj.obj (op T) :=
  Abelian.Ext.linearEquiv₀.trans (SheafLinearSections.homLinearEquiv J R hT M)

theorem degreeZeroLinearEquiv_mk (M : Sheaf J (ModuleCat.{w} R)) (a : constantUnit J R ⟶ M) :
    degreeZeroLinearEquiv J R hT M (Abelian.Ext.mk₀ a) = SheafLinearSections.homLinearEquiv J R hT M a := by
  exact congrArg (SheafLinearSections.homLinearEquiv J R hT M) (Abelian.Ext.linearEquiv₀.apply_symm_apply a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafLinearSections

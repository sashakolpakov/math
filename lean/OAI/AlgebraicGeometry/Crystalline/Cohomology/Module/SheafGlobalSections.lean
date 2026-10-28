import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections
import Mathlib.CategoryTheory.Sites.GlobalSections

/-! # Sheaf Global Sections -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.SheafGlobalSections.ModuleSheafGlobalSections

noncomputable section

/-! # Coefficient-linear global sections and the original degree-zero Ext functor -/

open _root_.CategoryTheory Limits

universe u v w z

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  [HasGlobalSectionsFunctor J (ModuleCat.{w} R)]

instance linear : (Sheaf.Γ J (ModuleCat.{w} R)).Linear R where
  map_smul {M N} f r := by
    apply (Sheaf.isLimitConeΓ N).hom_ext
    intro U
    change (Sheaf.Γ J (ModuleCat.{w} R)).map (r • f) ≫ Sheaf.ΓRes N U =
      (r • (Sheaf.Γ J (ModuleCat.{w} R)).map f) ≫ Sheaf.ΓRes N U
    rw [Sheaf.ΓRes_naturality, Linear.smul_comp, Sheaf.ΓRes_naturality]
    exact Linear.comp_smul _ _ _ (Sheaf.ΓRes M U) r (f.hom.app U)

def coefficientEquiv (M : Sheaf J (ModuleCat.{w} R)) :
    (NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J ⟶ M) ≃ₗ[R]
      (Sheaf.Γ J (ModuleCat.{w} R)).obj M :=
  (NumberTheory.PadicHodge.IntegralComparison.LinearAdjunction.homLinearEquiv R (constantSheafΓAdj J (ModuleCat.{w} R))
    (ModuleCat.of R R) M).trans
      ((ModuleCat.homLinearEquiv (S := R)).trans (LinearMap.ringLmapEquivSelf R R _))

theorem coefficientEquiv_natural {M N : Sheaf J (ModuleCat.{w} R)}
    (a : NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J ⟶ M) (b : M ⟶ N) :
    coefficientEquiv R J N (a ≫ b) = (Sheaf.Γ J (ModuleCat.{w} R)).map b (coefficientEquiv R J M a) :=
  congrArg (fun f : ModuleCat.of R R ⟶ (Sheaf.Γ J (ModuleCat.{w} R)).obj N => f (1 : R))
    ((constantSheafΓAdj J (ModuleCat.{w} R)).homEquiv_naturality_right a b)

variable [HasExt.{max u w z} (Sheaf J (ModuleCat.{w} R))]

def equivalence (M : Sheaf J (ModuleCat.{w} R)) :
    Abelian.Ext.{max u w z} (NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) M 0 ≃ₗ[R]
      ULift.{max u z} ((Sheaf.Γ J (ModuleCat.{w} R)).obj M) :=
  Abelian.Ext.linearEquiv₀.trans ((coefficientEquiv R J M).trans ULift.moduleEquiv.symm)

theorem equivalence_mk (M : Sheaf J (ModuleCat.{w} R))
    (a : NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J ⟶ M) :
    equivalence R J M (Abelian.Ext.mk₀ a) = ULift.up (coefficientEquiv R J M a) :=
  congrArg (fun b => ULift.up (coefficientEquiv R J M b)) (Abelian.Ext.linearEquiv₀.apply_symm_apply a)

def iso : NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R
    (NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) 0 ≅
      Sheaf.Γ J (ModuleCat.{w} R) ⋙ ModuleCat.uliftFunctor.{max u z, w} R :=
  NatIso.ofComponents (fun M => (equivalence R J M).toModuleIso) (by
    intro M N b
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := (Abelian.Ext.mk₀_bijective
      (NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) M).2 x
    have h := (congrArg (equivalence R J N) (Abelian.Ext.mk₀_comp_mk₀ a b)).trans
      ((equivalence_mk R J N (a ≫ b)).trans (congrArg ULift.up (coefficientEquiv_natural R J a b)))
    exact h.trans (congrArg
      (fun y : ULift.{max u z} ((Sheaf.Γ J (ModuleCat.{w} R)).obj M) =>
        ULift.up ((Sheaf.Γ J (ModuleCat.{w} R)).map b y.down))
      (equivalence_mk R J M a).symm))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.SheafGlobalSections.ModuleSheafGlobalSections

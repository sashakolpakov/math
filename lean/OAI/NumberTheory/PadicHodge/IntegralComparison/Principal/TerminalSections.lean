import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.TerminalScalars

/-! # Terminal Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.TerminalSections

noncomputable section

/-! Evaluation at the terminal principal open is the original affine
section functor, through literal restriction of module sections. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

def restriction (M : X.Modules) : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, SectionPresheaf.openSubset U (⊤_ (SectionPresheaf.Index U))) where
  toFun := M.presheaf.map (SectionPresheaf.inclusion U (⊤_ (SectionPresheaf.Index U))).op
  map_add' := map_add _
  map_smul' a m := by
    change M.presheaf.map (SectionPresheaf.inclusion U (⊤_ (SectionPresheaf.Index U))).op (a • m) =
      (X.presheaf.map (SectionPresheaf.inclusion U (⊤_ (SectionPresheaf.Index U))).op a) •
        M.presheaf.map (SectionPresheaf.inclusion U (⊤_ (SectionPresheaf.Index U))).op m
    exact M.map_smul (SectionPresheaf.inclusion U (⊤_ (SectionPresheaf.Index U))) a m

def equiv (M : X.Modules) : Γ(M, U) ≃ₗ[Γ(X, U)] Γ(M, SectionPresheaf.openSubset U (⊤_ (SectionPresheaf.Index U))) := by
  letI := TerminalScalars.inclusion_isIso U hU
  exact LinearEquiv.ofBijective (restriction U M)
    (ConcreteCategory.bijective_of_isIso (M.presheaf.map (SectionPresheaf.inclusion U (⊤_ (SectionPresheaf.Index U))).op))

theorem equiv_apply (M : X.Modules) (m : Γ(M, U)) : equiv U hU M m =
    M.presheaf.map (SectionPresheaf.inclusion U (⊤_ (SectionPresheaf.Index U))).op m := rfl

def iso : Affine.ModuleExactSections.sections U ≅
    ModuleFunctor.functor U hU ⋙
      (evaluation (SectionPresheaf.Index U)ᵒᵖ (ModuleCat Γ(X, U))).obj (op (⊤_ (SectionPresheaf.Index U))) :=
  NatIso.ofComponents (fun M => (equiv U hU M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact (PresheafOfModules.naturality_apply f.val (SectionPresheaf.inclusion U (⊤_ (SectionPresheaf.Index U))).op m).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.TerminalSections

import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ModuleFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleExactSections

/-! # At One -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOne

noncomputable section

/-! Evaluation of the native principal section diagram at the unit
coefficient is canonically the original section module on the ambient
open. The map is literal restriction and is natural in module sheaves. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X : Scheme.{u}} (U : X.Opens)

def object : SectionPresheaf.Index U := ⟨1⟩

theorem open_eq : SectionPresheaf.openSubset U (object U) = U := X.basicOpen_one

instance inclusion_isIso : IsIso (SectionPresheaf.inclusion U (object U)) := by
  have h : SectionPresheaf.inclusion U (object U) = eqToHom (open_eq U) := Subsingleton.elim _ _
  rw [h]
  infer_instance

def restriction (M : X.Modules) : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, SectionPresheaf.openSubset U (object U)) where
  toFun := M.presheaf.map (SectionPresheaf.inclusion U (object U)).op
  map_add' := map_add _
  map_smul' a m := by
    change M.presheaf.map (SectionPresheaf.inclusion U (object U)).op (a • m) =
      (X.presheaf.map (SectionPresheaf.inclusion U (object U)).op a) •
        M.presheaf.map (SectionPresheaf.inclusion U (object U)).op m
    exact M.map_smul (SectionPresheaf.inclusion U (object U)) a m

def equiv (M : X.Modules) : Γ(M, U) ≃ₗ[Γ(X, U)] Γ(M, SectionPresheaf.openSubset U (object U)) :=
  LinearEquiv.ofBijective (restriction U M)
    (ConcreteCategory.bijective_of_isIso (M.presheaf.map (SectionPresheaf.inclusion U (object U)).op))

theorem equiv_apply (M : X.Modules) (m : Γ(M, U)) : equiv U M m =
    M.presheaf.map (SectionPresheaf.inclusion U (object U)).op m := rfl

variable (hU : IsAffineOpen U)

def iso : Affine.ModuleExactSections.sections U ≅
    ModuleFunctor.functor U hU ⋙
      (evaluation (SectionPresheaf.Index U)ᵒᵖ (ModuleCat Γ(X, U))).obj (op (object U)) :=
  NatIso.ofComponents (fun M => (equiv U M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact (PresheafOfModules.naturality_apply f.val (SectionPresheaf.inclusion U (object U)).op m).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOne

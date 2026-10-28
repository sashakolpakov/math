import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomSectionsEquiv
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections

/-! # Hom Principal Ext -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomPrincipalExt

noncomputable section

/-! To compare internal-Hom sections on a principal affine subopen,
it suffices to evaluate on restrictions of the original sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) (r : Γ(X, U))
  (M N : X.Modules) [M.IsQuasicoherent]
  (a b : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, AffinePrincipal.Sections.openSubset U r))

include hU in
theorem ext
    (h : ∀ m : Γ(M, U),
      ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen M N (AffinePrincipal.Sections.openSubset U r) a (M.presheaf.map (AffinePrincipal.Sections.inclusion U r).op m) =
        ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen M N (AffinePrincipal.Sections.openSubset U r) b (M.presheaf.map (AffinePrincipal.Sections.inclusion U r).op m)) :
    a = b := by
  apply (HomSectionsEquiv.equiv (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) M N).injective
  apply LinearMap.ext
  intro m
  obtain ⟨z, rfl⟩ := (AffinePrincipal.Sections.iso U hU r M).surjective m
  induction z using TensorProduct.inductionOn with
  | tmul s m =>
      simp only [AffinePrincipal.Sections.iso_tmul, HomSectionsEquiv.equiv_apply,
        map_smul, h]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomPrincipalExt

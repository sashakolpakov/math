import OAI.NumberTheory.PadicHodge.IntegralComparison.LineFrameBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.LinearHomBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Hom

/-! # Line Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.LineFrame

noncomputable section

/-! The compatible frame on a principal subopen is compatible with
the literal restriction of sections. Its quotient-valued inverse frame
therefore has the actual restriction formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) (r : Γ(X, U))
  (N : X.Modules) [N.IsQuasicoherent]

def restriction : (AffineOpen.InternalHom.sections U hU).obj N →ₛₗ[algebraMap Γ(X, U) Γ(X, Sections.openSubset U r)]
    (AffineOpen.InternalHom.sections (Sections.openSubset U r) (hU.basicOpen r)).obj N :=
  (Affine.ChartSections.iso (Sections.openSubset U r) (hU.basicOpen r) N).hom.hom.comp
    ((N.val.restrictₛₗ (Sections.inclusion U r).op).comp (Affine.ChartSections.iso U hU N).inv.hom)

theorem chartIso_one (x : (AffineOpen.InternalHom.sections U hU).obj N) :
    (Hom.Comparison.chartIso U hU r N).hom (1 ⊗ₜ[Γ(X, U)] x) =
      restriction U hU r N x := by
  obtain ⟨m, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Affine.ChartSections.iso U hU N).hom).surjective x
  rw [Hom.Comparison.chartIso_tmul, one_smul]
  change _ = (Affine.ChartSections.iso (Sections.openSubset U r) (hU.basicOpen r) N).hom
    (N.presheaf.map (Sections.inclusion U r).op
      ((Affine.ChartSections.iso U hU N).inv ((Affine.ChartSections.iso U hU N).hom m)))
  rw [Iso.hom_inv_id_apply]

variable (e : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(X, U) Γ(X, U))

def targetFrame : (AffineOpen.InternalHom.sections (Sections.openSubset U r) (hU.basicOpen r)).obj N ≅
    ModuleCat.of Γ(X, Sections.openSubset U r) Γ(X, Sections.openSubset U r) :=
  LinearHomBaseChange.compatibleFrame Γ(X, U) Γ(X, Sections.openSubset U r) _ _ e
    (Hom.Comparison.chartIso U hU r N)

theorem targetFrame_restriction (x : (AffineOpen.InternalHom.sections U hU).obj N) :
    (targetFrame U hU r N e).hom (restriction U hU r N x) =
      algebraMap Γ(X, U) Γ(X, Sections.openSubset U r) (e.hom x) := by
  let : IsLocalization.Away r Γ(X, Sections.openSubset U r) := hU.isLocalization_basicOpen r
  let : Module.Flat Γ(X, U) Γ(X, Sections.openSubset U r) :=
    IsLocalization.flat Γ(X, Sections.openSubset U r) (Submonoid.powers r)
  rw [← chartIso_one]
  exact (LinearHomBaseChange.compatibleFrame_tmul Γ(X, U) Γ(X, Sections.openSubset U r) _ _ e
    (Hom.Comparison.chartIso U hU r N) 1 x).trans (one_mul _)

variable (I : Ideal Γ(X, U)) (J : Ideal Γ(X, Sections.openSubset U r))
  (h : I ≤ J.comap (algebraMap Γ(X, U) Γ(X, Sections.openSubset U r)))

def lineMap := LineFrameBaseChange.lineMap Γ(X, U) Γ(X, Sections.openSubset U r)
  (algebraMap Γ(X, U) Γ(X, Sections.openSubset U r)) I J h _ _ (restriction U hU r N)

theorem lineFrame_symm_restriction (a : Γ(X, U) ⧸ I) :
    lineMap U hU r N I J h
      ((LineValuedKoszulPurity.lineFrame Γ(X, U) I ((AffineOpen.InternalHom.sections U hU).obj N) e).symm a) =
      (LineValuedKoszulPurity.lineFrame Γ(X, Sections.openSubset U r) J
        ((AffineOpen.InternalHom.sections (Sections.openSubset U r) (hU.basicOpen r)).obj N) (targetFrame U hU r N e)).symm
          (Ideal.quotientMap J (algebraMap Γ(X, U) Γ(X, Sections.openSubset U r)) h a) :=
  LineFrameBaseChange.lineFrame_symm_map Γ(X, U) Γ(X, Sections.openSubset U r)
    (algebraMap Γ(X, U) Γ(X, Sections.openSubset U r)) I J h _ _ (restriction U hU r N) e
    (targetFrame U hU r N e) (targetFrame_restriction U hU r N e) a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.LineFrame

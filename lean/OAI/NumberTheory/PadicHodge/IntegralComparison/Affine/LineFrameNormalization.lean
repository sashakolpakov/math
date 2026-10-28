import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalizationBase

/-! # Line Frame Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LineFrameNormalization.PrincipalOrientedResidue

noncomputable section

/-! A frame given in actual affine-chart coordinates is the same
frame used by the principal residue construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) (N : X.Modules)
  (eN : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(X, U) Γ(X, U))

def sectionFrame : Γ(N, U) ≃ₗ[Γ(X, U)] Γ(X, U) :=
  ((ChartSections.iso U hU N) ≪≫ eN).toLinearEquiv

theorem lineIso_sectionFrame : Principal.OrientedResidueNormalizationBase.lineIso U hU N (sectionFrame U hU N eN) = eN := by
  apply Iso.ext
  change (ChartSections.iso U hU N).inv ≫
      ((ChartSections.iso U hU N).hom ≫ eN.hom) = eN.hom
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LineFrameNormalization.PrincipalOrientedResidue

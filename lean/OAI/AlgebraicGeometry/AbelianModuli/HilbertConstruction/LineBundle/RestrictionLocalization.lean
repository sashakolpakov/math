import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenLineBundleLocalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.Localization

/-! # Restriction Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.RestrictionLocalization

noncomputable section

/-! Ordinary global-section restriction for a line bundle is localization on each principal affine base open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem lineBundle_restriction_localizes_on_base_basicOpen
    {X S : Scheme.{u}} [IsAffine S] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (f : X ⟶ S) (L : Line.Bundles.LineBundle X) (r : Γ(S, ⊤)) :
    IsLocalizedModule.Away r
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom L.sheaf).map (f ⁻¹ᵁ S.basicOpen r).leTop.op).hom := by
  have := OpenLineBundleLocalization.lineBundle_sections_localize_on_base_basicOpen f L r
  exact OpenPullback.Localization.openPullback_localization_implies_restriction f.appTop.hom L.sheaf
    (f ⁻¹ᵁ S.basicOpen r) (Submonoid.powers r)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.RestrictionLocalization

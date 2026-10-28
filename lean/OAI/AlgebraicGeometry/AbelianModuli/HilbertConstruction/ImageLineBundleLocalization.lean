import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.RestrictionLocalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PushforwardSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.ModuleSquares

/-! # Image Line Bundle Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ImageLineBundleLocalization

noncomputable section

/-! The actual direct-image presheaf of a line bundle localizes on principal opens of an affine target. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem lineBundle_directImage_sections_localize
    {X S : Scheme.{u}} [IsAffine S] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (f : X ⟶ S) (L : Line.Bundles.LineBundle X) (r : Γ(S, ⊤)) :
    IsLocalizedModule.Away r
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf (RingHom.id Γ(S, ⊤))
        ((Scheme.Modules.pushforward f).obj L.sheaf)).map (S.basicOpen r).leTop.op).hom := by
  let c := RingHom.id Γ(S, ⊤)
  have h := LineBundle.RestrictionLocalization.lineBundle_restriction_localizes_on_base_basicOpen f L r
  exact (Localized.ModuleSquares.isLocalizedModule_iff_of_linearEquiv_square (Submonoid.powers r) _ _
    (Coefficient.PushforwardSections.coefficientPushforwardSectionEquiv f c L.sheaf ⊤)
    (Coefficient.PushforwardSections.coefficientPushforwardSectionEquiv f c L.sheaf (S.basicOpen r))
    (Coefficient.PushforwardSections.coefficientPushforwardSectionEquiv_naturality f c L.sheaf (S.basicOpen r).leTop)).mpr h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ImageLineBundleLocalization

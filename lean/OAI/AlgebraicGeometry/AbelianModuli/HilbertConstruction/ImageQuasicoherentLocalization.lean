import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.QuasicoherentLocalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PushforwardSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.ModuleSquares

/-! # Image Quasicoherent Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ImageQuasicoherentLocalization

noncomputable section

/-! Direct-image quasicoherent sections localize on every principal open of the target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem quasicoherent_directImage_sections_localize
    {X S : Scheme.{u}} [X.IsSeparated] [CompactSpace X]
    (f : X ⟶ S) (M : X.Modules) [M.IsQuasicoherent] (r : Γ(S, ⊤)) :
    IsLocalizedModule.Away r
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf (RingHom.id Γ(S, ⊤))
        ((Scheme.Modules.pushforward f).obj M)).map (S.basicOpen r).leTop.op).hom := by
  let c := RingHom.id Γ(S, ⊤)
  have h := Base.QuasicoherentLocalization.quasicoherent_restriction_localizes_on_base_basicOpen f M r
  exact (Localized.ModuleSquares.isLocalizedModule_iff_of_linearEquiv_square (Submonoid.powers r) _ _
    (Coefficient.PushforwardSections.coefficientPushforwardSectionEquiv f c M ⊤)
    (Coefficient.PushforwardSections.coefficientPushforwardSectionEquiv f c M (S.basicOpen r))
    (Coefficient.PushforwardSections.coefficientPushforwardSectionEquiv_naturality f c M (S.basicOpen r).leTop)).mpr h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ImageQuasicoherentLocalization

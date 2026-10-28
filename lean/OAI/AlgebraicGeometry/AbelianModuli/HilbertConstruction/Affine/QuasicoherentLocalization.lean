import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.IsoImage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PushforwardSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.ModuleSquares

/-! # Quasicoherent Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentLocalization

noncomputable section

/-! Quasicoherent sections on any affine scheme localize on its intrinsic principal opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem affine_quasicoherent_sections_localize {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] (r : Γ(X, ⊤)) :
    IsLocalizedModule.Away r
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf (RingHom.id Γ(X, ⊤)) M).map (X.basicOpen r).leTop.op).hom := by
  let f := X.toSpecΓ
  let c := (Scheme.ΓSpecIso (.of Γ(X, ⊤))).inv.hom
  let N := (pushforward f).obj M
  let U : (Spec (.of Γ(X, ⊤))).Opens := PrimeSpectrum.basicOpen r
  have : N.IsQuasicoherent := Quasicoherent.IsoImage.modulePushforward_quasicoherent_of_isIso f M
  have ha : IsLocalizedModule.Away r ((Coefficient.ModulePresheaf.coefficientModulePresheaf c N).map U.leTop.op).hom :=
    (isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance r
  have hb := Localized.ModuleSquares.isLocalizedModule_of_linearEquiv_square (.powers r)
    ((Coefficient.ModulePresheaf.coefficientModulePresheaf c N).map U.leTop.op).hom
    ((Coefficient.ModulePresheaf.coefficientModulePresheaf (f.appTop.hom.comp c) M).map
      ((TopologicalSpace.Opens.map f.base).map U.leTop).op).hom
    (Coefficient.PushforwardSections.coefficientPushforwardSectionEquiv f c M ⊤)
    (Coefficient.PushforwardSections.coefficientPushforwardSectionEquiv f c M U)
    (Coefficient.PushforwardSections.coefficientPushforwardSectionEquiv_naturality f c M U.leTop)
  have hc : f.appTop.hom.comp c = RingHom.id Γ(X, ⊤) := by
    ext a
    change X.toSpecΓ.appTop ((Scheme.ΓSpecIso (.of Γ(X, ⊤))).inv a) = a
    rw [Scheme.toSpecΓ_appTop]
    exact (Scheme.ΓSpecIso (.of Γ(X, ⊤))).inv_hom_id_apply a
  rw [hc] at hb
  have hU : f ⁻¹ᵁ U = X.basicOpen r := X.toSpecΓ_preimage_basicOpen r
  change IsLocalizedModule.Away r
    ((Coefficient.ModulePresheaf.coefficientModulePresheaf (RingHom.id Γ(X, ⊤)) M).map
      (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op).hom at hb
  rw [hU] at hb
  exact hb

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentLocalization

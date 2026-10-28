import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.QuasicoherentLocalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocalizationRestrictScalars

/-! # Quasicoherent Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.QuasicoherentLocalization

noncomputable section

/-! Global quasicoherent section localization respects arbitrary base coefficient maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

theorem coefficientGlobalQuasicoherentSections_localize
    {X : Scheme.{u}} [X.IsSeparated] [CompactSpace X] {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) (M : X.Modules) [M.IsQuasicoherent] (r : R) :
    IsLocalizedModule.Away r
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf c M).map (X.basicOpen (c r)).leTop.op).hom := by
  have := Global.QuasicoherentLocalization.globalQuasicoherentSections_localize M (c r)
  exact LocalizationRestrictScalars.coefficientSection_localization_restrictScalars c (RingHom.id Γ(X, ⊤)) M
    (X.basicOpen (c r)) r

theorem quasicoherent_restriction_localizes_on_base_basicOpen
    {X S : Scheme.{u}} [X.IsSeparated] [CompactSpace X]
    (f : X ⟶ S) (M : X.Modules) [M.IsQuasicoherent] (r : Γ(S, ⊤)) :
    IsLocalizedModule.Away r
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom M).map (f ⁻¹ᵁ S.basicOpen r).leTop.op).hom := by
  have h := coefficientGlobalQuasicoherentSections_localize f.appTop.hom M r
  exact (congrArg (fun U : X.Opens ↦ IsLocalizedModule.Away r
    ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom M).map U.leTop.op).hom)
      (f.preimage_basicOpen_top r)).mpr h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.QuasicoherentLocalization

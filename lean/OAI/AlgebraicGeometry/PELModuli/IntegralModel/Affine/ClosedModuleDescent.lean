import OAI.AlgebraicGeometry.PELModuli.IntegralModel.QuotientModuleDescent
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineGeometric
import OAI.AlgebraicGeometry.SheafCohomology.Projective.QuasicoherentAffinePullback
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Closed Module Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ClosedModuleDescent

noncomputable section

/-! The actual pullback-pushforward unit is invertible for a quasicoherent
module annihilated by the ideal of an affine closed immersion. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules OAI.AlgebraicGeometry.SheafCohomology.Projective.QuasicoherentAffinePullback

universe u

theorem affineModule_unit_isIso_of_kernel_annihilates
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (hf : Function.Surjective f.appTop.hom)
    (M : Y.Modules) [M.IsQuasicoherent]
    (h : RingHom.ker f.appTop.hom ≤ Module.annihilator Γ(Y, ⊤) Γ(M, ⊤)) :
    IsIso ((pullbackPushforwardAdjunction f).unit.app M) := by
  let P := (pullback f).obj M
  have : P.IsQuasicoherent := SheafCohomology.Projective.QuasicoherentAffinePullback.affine_pullback_quasicoherent f M
  have : ((pushforward f).obj P).IsQuasicoherent :=
    SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f
  let a : M ⟶ (pushforward f).obj P := (pullbackPushforwardAdjunction f).unit.app M
  have hunit : IsIso ((ModuleCat.extendRestrictScalarsAdj f.appTop.hom).unit.app
      ((Quotients.FiniteDescent.AffineSectionIs.Construction.AffineSectionAdjunction.sections Y).obj M)) :=
    QuotientModuleDescent.quotientModule_unit_isIso f.appTop.hom hf _ h
  have he : IsIso ((Quotients.FiniteDescent.AffineSectionIs.Construction.AffineSectionAdjunction.sections Y).map a ≫
      (Quotients.FiniteDescent.AffineSectionIs.Construction.AffineSectionAdjunction.pushforwardIso f).hom.app P) := by
    rw [← Quotients.FiniteDescent.AffineGeometric.Construction.AffineGeometricSections.normalization f M, Adjunction.homEquiv_unit]
    infer_instance
  have ha : IsIso ((Quotients.FiniteDescent.AffineSectionIs.Construction.AffineSectionAdjunction.sections Y).map a) :=
    IsIso.of_isIso_comp_right _ ((Quotients.FiniteDescent.AffineSectionIs.Construction.AffineSectionAdjunction.pushforwardIso f).hom.app P)
  exact SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isIso_of_isQuasicoherent_of_isIso_app_top
    (M := M) (N := (pushforward f).obj P) a ha

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ClosedModuleDescent

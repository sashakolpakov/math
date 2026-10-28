import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TargetQuasicoherentImage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.QuasicoherenceLocality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionPushforward

/-! # Image -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Image

noncomputable section

/-! Quasi-compact separated direct images preserve quasicoherence over every scheme base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem quasiCompact_separated_directImage_affine
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [QuasiCompact f] [IsSeparated f] (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  let N := (pushforward f).obj M
  have h : ((pushforward (f ≫ S.toSpecΓ)).obj M).IsQuasicoherent :=
    Affine.TargetQuasicoherentImage.quasiCompact_separated_directImage_over_spectrum (f ≫ S.toSpecΓ) M
  have h' : ((pushforward S.toSpecΓ).obj N).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(S, ⊤)).ringCatSheaf).prop_of_iso
      ((pushforwardComp f S.toSpecΓ).app M).symm h
  have h'' : (((pushforward S.toSpecΓ).obj N).restrict S.toSpecΓ).IsQuasicoherent := inferInstance
  exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    ((restrictFunctorAdjCounitIso S.toSpecΓ).app N) h''

theorem quasiCompact_separated_directImage_quasicoherent
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [IsSeparated f] (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  apply Module.QuasicoherenceLocality.module_quasicoherent_of_affine_restrictions
  intro U
  let V := f ⁻¹ᵁ U.1
  let q := f ∣_ U.1
  have : IsAffine U.1.toScheme := U.2
  have h : ((pushforward q).obj (M.restrict V.ι)).IsQuasicoherent :=
    quasiCompact_separated_directImage_affine q (M.restrict V.ι)
  let e : (((pushforward f).obj M).restrict U.1.ι) ≅
      (pushforward q).obj (M.restrict V.ι) :=
    Open.RestrictionPushforward.restrictPushforwardIsoOfIsPullbackApp f q V.ι U.1.ι
      (isPullback_morphismRestrict f U.1) M
  exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso e.symm h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Image

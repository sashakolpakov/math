import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TargetLineBundleQuasicoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.QuasicoherenceLocality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionPushforward

/-! # Line Bundle Image -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.LineBundleImage

noncomputable section

/-! Proper direct images of actual line bundles are quasicoherent over every scheme base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem proper_lineBundle_directImage_quasicoherent_affine
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [IsProper f] (L : Line.Bundles.LineBundle X) :
    ((pushforward f).obj L.sheaf).IsQuasicoherent := by
  let M := (pushforward f).obj L.sheaf
  have h : ((pushforward (f ≫ S.toSpecΓ)).obj L.sheaf).IsQuasicoherent :=
    Affine.TargetLineBundleQuasicoherence.proper_lineBundle_directImage_quasicoherent_over_spectrum (f ≫ S.toSpecΓ) L
  have h' : ((pushforward S.toSpecΓ).obj M).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(S, ⊤)).ringCatSheaf).prop_of_iso
      ((pushforwardComp f S.toSpecΓ).app L.sheaf).symm h
  have h'' : (((pushforward S.toSpecΓ).obj M).restrict S.toSpecΓ).IsQuasicoherent := inferInstance
  exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    ((restrictFunctorAdjCounitIso S.toSpecΓ).app M) h''

theorem proper_lineBundle_directImage_quasicoherent
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (L : Line.Bundles.LineBundle X) :
    ((pushforward f).obj L.sheaf).IsQuasicoherent := by
  apply Module.QuasicoherenceLocality.module_quasicoherent_of_affine_restrictions
  intro U
  let V := f ⁻¹ᵁ U.1
  let q := f ∣_ U.1
  have : IsAffine U.1.toScheme := U.2
  have h : ((pushforward q).obj (L.pullback V.ι).sheaf).IsQuasicoherent :=
    proper_lineBundle_directImage_quasicoherent_affine q (L.pullback V.ι)
  let e : (((pushforward f).obj L.sheaf).restrict U.1.ι) ≅
      (pushforward q).obj (L.pullback V.ι).sheaf :=
    Open.RestrictionPushforward.restrictPushforwardIsoOfIsPullbackApp f q V.ι U.1.ι
      (isPullback_morphismRestrict f U.1) L.sheaf ≪≫
        (pushforward q).mapIso ((restrictFunctorIsoPullback V.ι).app L.sheaf)
  exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso e.symm h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.LineBundleImage

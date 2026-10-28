import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChowLinePushforward

/-! # Chow Generic Line -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChowGenericLine

noncomputable section

/-! A line-bundle direct image on a Chow modification is an actual
line bundle over the specified nonempty common affine open. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

def lineBundlePushforwardIso_of_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    (pushforward f).obj L.sheaf ≅ (L.pullback (inv f)).sheaf :=
  ((SheafCohomology.Projective.Quasicoherent.Scheme.Modules.restrictFunctor_inv_restrictFunctor_hom_id (asIso f).symm).app
      ((pushforward f).obj L.sheaf)).symm ≪≫
    (restrictFunctor (inv f)).mapIso ((restrictFunctorAdjCounitIso f).app L.sheaf) ≪≫
      (restrictFunctorIsoPullback (inv f)).app L.sheaf

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} (D : Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.Model f) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle D.scheme)

def chowPushforwardLineOnCommon : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle D.cover.common.toScheme := by
  letI : IsIso (D.projection ∣_ D.cover.common) := D.isIso_restrict
  exact (L.pullback (D.projection ⁻¹ᵁ D.cover.common).ι).pullback
    (inv (D.projection ∣_ D.cover.common))

def chowPushforward_restrictCommon_iso :
    (((pushforward D.projection).obj L.sheaf).restrict D.cover.common.ι) ≅
      (chowPushforwardLineOnCommon D L).sheaf := by
  let q := D.projection ∣_ D.cover.common
  let V := D.projection ⁻¹ᵁ D.cover.common
  letI : IsIso q := D.isIso_restrict
  exact SheafCohomology.Projective.ModuleRestrictPushforward.Scheme.Modules.restrictPushforwardIsoOfIsPullbackApp D.projection q V.ι D.cover.common.ι
    (isPullback_morphismRestrict D.projection D.cover.common) L.sheaf ≪≫
    (pushforward q).mapIso ((restrictFunctorIsoPullback V.ι).app L.sheaf) ≪≫
    lineBundlePushforwardIso_of_isIso q (L.pullback V.ι)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChowGenericLine

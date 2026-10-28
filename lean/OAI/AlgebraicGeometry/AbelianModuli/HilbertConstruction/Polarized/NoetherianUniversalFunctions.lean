import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.NoetherianAffineProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.UniversalGlobalFunctions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.BaseChangeFunctions

/-! # Noetherian Universal Functions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A polarized abelian scheme over a locally Noetherian base has exactly base global functions after every scheme base change. The necessary local projective presentations are constructed. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.localRingPullback_globalFunctions_isIso_of_locallyNoetherian
    {R : Type u} [CommRing R] [IsLocalRing R] (b : Spec (.of R) ⟶ S) :
    IsIso (A.pullback b).abelian.scheme.hom.appTop := by
  let s := b (IsLocalRing.closedPoint R)
  have hR : IsNoetherianRing (S.presheaf.stalk s) :=
    AlgebraicGeometry.instIsNoetherianRingCarrierStalkCommRingCatPresheafOfIsLocallyNoetherian
      (X := S) (x := s)
  let c := S.fromSpecStalk s
  let q := Spec.map (Scheme.stalkClosedPointTo b)
  have hqc : q ≫ c = b := Scheme.Spec_stalkClosedPointTo_fromSpecStalk b
  let B := A.pullback c
  have : IsNoetherianRing Γ(Spec (S.presheaf.stalk s), ⊤) :=
    isNoetherianRing_of_ringEquiv (S.presheaf.stalk s)
      (Scheme.ΓSpecIso (S.presheaf.stalk s)).symm.commRingCatIsoToRingEquiv
  have hΓ := @AffineProjective.UniversalConstants.affineProjectivePresentation_baseChange_globalFunctions_isIso
    (S.presheaf.stalk s) _ hR B.abelian.scheme
    (inferInstanceAs (IsProper B.abelian.scheme.hom))
    (inferInstanceAs (Smooth B.abelian.scheme.hom))
    (inferInstanceAs (GeometricallyConnected B.abelian.scheme.hom))
    B.projectivePresentation_of_noetherian_affine η[B.abelian.scheme].left η[B.abelian.scheme].w
    _ _ _ _ _
    (IsPullback.of_hasPullback B.abelian.scheme.hom q)
  have hΓ' := (HilbertConstruction.Over.IsoGlobalFunctions.overIso_appTop_isIso_iff ((Over.pullbackComp q c).app A.abelian.scheme)).mpr hΓ
  change IsIso (pullback.snd A.abelian.scheme.hom (q ≫ c)).appTop at hΓ'
  rw [hqc] at hΓ'
  exact hΓ'

theorem PolarizationData.PolarizedAbelianWithFullLevel.cartesian_globalFunctions_isIso_of_locallyNoetherian
    {T Y : Scheme.{u}} {a : Y ⟶ A.abelian.scheme.left} {b : Y ⟶ T} {c : T ⟶ S}
    (H : IsPullback a b A.abelian.scheme.hom c) : IsIso b.appTop :=
  Universal.GlobalFunctionsLocalCriterion.universal_globalFunctions_isIso_of_localRingConstants A.abelian.scheme.hom
    η[A.abelian.scheme].left η[A.abelian.scheme].w
    (fun _ _ _ d => A.localRingPullback_globalFunctions_isIso_of_locallyNoetherian d) H

theorem PolarizationData.PolarizedAbelianWithFullLevel.pullback_globalFunctions_isIso_of_locallyNoetherian {T : Scheme.{u}} (f : T ⟶ S) :
    IsIso (A.pullback f).abelian.scheme.hom.appTop :=
  A.cartesian_globalFunctions_isIso_of_locallyNoetherian
    (IsPullback.of_hasPullback A.abelian.scheme.hom f)

theorem PolarizationData.PolarizedAbelianWithFullLevel.pullback_zero_globalFunctions_isIso_of_locallyNoetherian {T : Scheme.{u}} (f : T ⟶ S) :
    IsIso η[(A.pullback f).abelian.scheme].left.appTop := by
  have := A.pullback_globalFunctions_isIso_of_locallyNoetherian f
  exact Proper.FieldBaseChangeConstants.section_globalFunctions_isIso (A.pullback f).abelian.scheme.hom
    η[(A.pullback f).abelian.scheme].left η[(A.pullback f).abelian.scheme].w

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

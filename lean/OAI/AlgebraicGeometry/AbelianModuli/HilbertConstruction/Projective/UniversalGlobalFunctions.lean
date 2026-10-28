import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.UniversalConstants
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Universal Global Functions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.UniversalGlobalFunctions

noncomputable section

/-! Pointed proper smooth geometrically connected projective families over locally noetherian bases have only base global functions after every scheme base change, including nonnoetherian and nonreduced tests. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem projectivePresentation_localRingPullback_globalFunctions_isIso
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : Over S} [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom]
    (P : ProjectivePresentations.ProjectivePresentation X) (x : S ⟶ X.left) (hx : x ≫ X.hom = 𝟙 _)
    {A : Type u} [CommRing A] [IsLocalRing A] (b : Spec (.of A) ⟶ S) :
    IsIso (pullback.snd X.hom b).appTop := by
  let s := b (IsLocalRing.closedPoint A)
  have hR : IsNoetherianRing (S.presheaf.stalk s) :=
    AlgebraicGeometry.instIsNoetherianRingCarrierStalkCommRingCatPresheafOfIsLocallyNoetherian
      (X := S) (x := s)
  let c := S.fromSpecStalk s
  let q := Spec.map (Scheme.stalkClosedPointTo b)
  have hqc : q ≫ c = b := Scheme.Spec_stalkClosedPointTo_fromSpecStalk b
  let σ := PointedFamilyFiberConnectedness.schemeSectionBaseChange X.hom x hx c
  have hσ : σ ≫ pullback.snd X.hom c = 𝟙 _ := PointedFamilyFiberConnectedness.schemeSectionBaseChange_section X.hom x hx c
  have hp : IsProper ((Over.pullback c).obj X).hom :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback X.hom c) inferInstance
  have hs : Smooth ((Over.pullback c).obj X).hom :=
    smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback X.hom c) inferInstance
  have hg : GeometricallyConnected ((Over.pullback c).obj X).hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) (IsPullback.of_hasPullback X.hom c) inferInstance
  have hΓ := @AffineProjective.UniversalConstants.affineProjectivePresentation_baseChange_globalFunctions_isIso
    (S.presheaf.stalk s) _ hR ((Over.pullback c).obj X) hp hs hg (P.baseChange c) σ hσ
    _ _ _ _ _ (IsPullback.of_hasPullback ((Over.pullback c).obj X).hom q)
  have hΓ' := (HilbertConstruction.Over.IsoGlobalFunctions.overIso_appTop_isIso_iff ((Over.pullbackComp q c).app X)).mpr hΓ
  change IsIso (pullback.snd X.hom (q ≫ c)).appTop at hΓ'
  rw [hqc] at hΓ'
  exact hΓ'

theorem projectivePresentation_baseChange_globalFunctions_isIso
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : Over S} [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom]
    (P : ProjectivePresentations.ProjectivePresentation X) (x : S ⟶ X.left) (hx : x ≫ X.hom = 𝟙 _)
    {T Y : Scheme.{u}} {a : Y ⟶ X.left} {b : Y ⟶ T} {c : T ⟶ S}
    (H : IsPullback a b X.hom c) : IsIso b.appTop :=
  Universal.GlobalFunctionsLocalCriterion.universal_globalFunctions_isIso_of_localRingConstants X.hom x hx
    (fun _ _ _ d => projectivePresentation_localRingPullback_globalFunctions_isIso P x hx d) H

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.UniversalGlobalFunctions

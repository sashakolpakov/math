import OAI.AlgebraicGeometry.HilbertScheme.Presentations.StalkIsomorphismFromRestriction

/-! # Restricted Isomorphism Stalks -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.RestrictedIsomorphismStalks

noncomputable section

/-! Restricting the target commutes with testing a morphism for
isomorphism on local spectra. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y T : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

theorem isIso_pullback_restrict_iff (g : T ⟶ U.toScheme) :
    IsIso (pullback.fst g (f ∣_ U)) ↔ IsIso (pullback.fst (g ≫ U.ι) f) := by
  rw [← (isPullback_morphismRestrict f U).isoPullback_hom_fst,
    PullbackIsomorphismTransport.isIso_pullback_fst_comp_right_iff, IteratedPullbackIsomorphism.isIso_pullback_fst_iterated_iff]

theorem isIso_pullback_restrict_stalk_iff (u : U) :
    IsIso (pullback.fst (U.toScheme.fromSpecStalk u) (f ∣_ U)) ↔
      IsIso (pullback.fst (Y.fromSpecStalk (U.ι u)) f) := by
  rw [isIso_pullback_restrict_iff]
  have he : Spec.map (U.ι.stalkMap u) ≫ Y.fromSpecStalk (U.ι u) =
      U.toScheme.fromSpecStalk u ≫ U.ι := Scheme.SpecMap_stalkMap_fromSpecStalk U.ι
  let : IsIso (U.ι.stalkMap u) := ((IsOpenImmersion.iff_isIso_stalkMap
      (X := U.toScheme) (Y := Y) (f := U.ι)).mp
    (inferInstanceAs (IsOpenImmersion U.ι))).2 u
  let : IsIso (Spec.map (U.ι.stalkMap u)) := inferInstance
  rw [← he]
  exact OpenPullbackIsomorphismTransport.isIso_pullback_fst_comp_left_iff _ _ _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.RestrictedIsomorphismStalks

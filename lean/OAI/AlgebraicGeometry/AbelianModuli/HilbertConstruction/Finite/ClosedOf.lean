import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ClosedImmersionFieldDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.CoverPullbacks
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Closed Of -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ClosedOf

noncomputable section

/-! A finite map over an affine spectrum is a closed immersion if every
field-valued base change is a closed immersion. The affine criterion is
applied to the actual pullbacks of affine target charts. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem finite_overMap_closedImmersion_of_field_baseChanges
    (R : Type u) [CommRing R] {X Y : Over (Spec (.of R))}
    (f : X ⟶ Y) [IsFinite f.left]
    (h : ∀ (K : Type u) [Field K] [Algebra R K],
      IsClosedImmersion (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f).left)) :
    IsClosedImmersion f.left := by
  let C := Y.left.affineCover
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) C
  intro i
  let b := Embedded.FamilyOpenCover.overOpenCoverMap Y C i
  let q : pullback f b ⟶ Embedded.FamilyOpenCover.overOpenCoverObject Y C i := pullback.snd f b
  have H : IsPullback (pullback.fst f b).left q.left f.left b.left :=
    (IsPullback.of_hasPullback f b).map (Over.forget _)
  have : IsFinite q.left := MorphismProperty.of_isPullback H inferInstance
  have : IsAffine (Embedded.FamilyOpenCover.overOpenCoverObject Y C i).left :=
    inferInstanceAs (IsAffine (C.X i))
  have : IsAffine (pullback f b).left := isAffine_of_isAffineHom q.left
  have hq : IsClosedImmersion q.left :=
    ClosedImmersionFieldDetection.finite_affine_overMap_closedImmersion_of_field_baseChanges R q (by
      intro K _ _
      let P := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      have : IsClosedImmersion (P.map f).left := h K
      have HK : IsPullback (P.map (pullback.fst f b)).left (P.map q).left
          (P.map f).left (P.map b).left :=
        ((IsPullback.of_hasPullback f b).map P).map (Over.forget _)
      exact MorphismProperty.of_isPullback HK inferInstance)
  have hc : IsClosedImmersion (H.isoPullback.inv ≫ q.left) := inferInstance
  have he : H.isoPullback.inv ≫ q.left = C.pullbackHom f.left i := H.isoPullback_inv_snd
  exact he ▸ hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ClosedOf

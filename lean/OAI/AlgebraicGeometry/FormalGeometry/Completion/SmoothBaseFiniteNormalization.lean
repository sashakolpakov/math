import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.Normalization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothStalkDomains
import OAI.AlgebraicGeometry.FormalGeometry.Completion.UnramifiedNormalization

/-! # Smooth Base Finite Normalization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothBaseFiniteNormalization.Construction

noncomputable section

/-!
# Completion: finite normalization over the actual smooth integral base

The affine trace bound applies on every nonempty affine chart. Relative
normalization commutes with these open base changes, so the finite maps
descend to the actual normalization factor.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- Finiteness of the actual integral factor over a smooth integral field scheme. -/
theorem smooth_base_proper_fromNormalization_finite (K : Type u) [Field K]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (pY : Y ⟶ Spec (CommRingCat.of K)) [Smooth pY]
    (f : X ⟶ Y) [IsProper f] [Surjective f] [FormallyUnramified f.fromNormalization] :
    IsFinite f.fromNormalization := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) Y.affineCover]
  intro i
  let R := Y.affineOpenCover.X i
  let g : Spec R ⟶ Y := Y.affineOpenCover.f i
  change IsFinite (pullback.snd f.fromNormalization g)
  rcases isEmpty_or_nonempty (Spec R) with hZ | hZ
  · have := hZ
    infer_instance
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion g
  have : IsDomain R := (affine_isIntegral_iff R).mp inferInstance
  have : IsLocallyNoetherian (Spec R) := LocallyOfFiniteType.isLocallyNoetherian (g ≫ pY)
  have : IsNoetherianRing R := (isLocallyNoetherian_Spec).mp inferInstance
  have : IsIntegrallyClosed Γ(Spec R, ⊤) :=
    SmoothStalkDomains.Construction.smooth_field_affine_sections_isIntegrallyClosed K (g ≫ pY) ⊤ (isAffineOpen_top _)
  have : IsIntegrallyClosed R := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  let f' := pullback.snd f g
  have : Surjective f' := inferInstance
  have : Nonempty (pullback f g : Scheme.{u}) :=
    ⟨(f'.surjective (Nonempty.some hZ)).choose⟩
  have : IsIntegral (pullback f g) := isIntegral_of_isOpenImmersion (pullback.fst f g)
  have : FormallyUnramified f'.fromNormalization := by
    have H : FormallyUnramified
        (f.normalizationPullback g ≫ pullback.snd f.fromNormalization g) :=
      MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance
        (MorphismProperty.pullback_snd _ _ inferInstance)
    simpa only [Scheme.Hom.normalizationPullback_snd] using H
  have : IsFinite f'.fromNormalization := Finite.Normalization.Construction.normal_base_proper_fromNormalization_finite R f'
  have H : IsFinite (f.normalizationPullback g ≫ pullback.snd f.fromNormalization g) := by
    simpa only [Scheme.Hom.normalizationPullback_snd] using this
  exact (MorphismProperty.cancel_left_of_respectsIso @IsFinite
    (f.normalizationPullback g) (pullback.snd f.fromNormalization g)).mp H

/-- The finite normalization factor of the actual proper smooth family, with all hypotheses
on the original smooth proper field schemes. -/
theorem proper_smooth_fromNormalization_finite (K : Type u) [Field K]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (pX : X ⟶ Spec (CommRingCat.of K)) [IsProper pX] [Smooth pX]
    (pY : Y ⟶ Spec (CommRingCat.of K)) [Smooth pY]
    (f : X ⟶ Y) [IsProper f] [Smooth f] [Surjective f] : IsFinite f.fromNormalization := by
  have := UnramifiedNormalization.Construction.proper_smooth_fromNormalization_formallyUnramified K pX f
  exact smooth_base_proper_fromNormalization_finite K pY f

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothBaseFiniteNormalization.Construction

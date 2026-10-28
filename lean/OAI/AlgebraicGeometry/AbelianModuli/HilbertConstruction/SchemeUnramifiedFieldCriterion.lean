import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.UnramifiedFieldCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedPullbackRefinements

/-! # Scheme Unramified Field Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeUnramifiedFieldCriterion

noncomputable section

/-! Locally finite-type morphisms are formally unramified exactly when all field-valued base changes are formally unramified. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem formallyUnramified_of_fieldPullbacks_affineTarget {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) [LocallyOfFiniteType f]
    (h : ∀ (K : Type u) [Field K] (b : Spec (.of K) ⟶ Spec R),
      FormallyUnramified (pullback.snd f b)) : FormallyUnramified f := by
  have : IsZariskiLocalAtSource (@FormallyUnramified : MorphismProperty Scheme.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ RingHom.FormallyUnramified inferInstance
  wlog hX : ∃ S : CommRingCat.{u}, X = Spec S generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := (@FormallyUnramified : MorphismProperty Scheme.{u})) X.affineCover]
    intro i
    apply this (X.affineCover.f i ≫ f) ?_ ⟨_, rfl⟩
    intro K _ b
    have := h K b
    exact UnramifiedPullbackRefinements.unramified_pullback_precomp_open f (X.affineCover.f i) b
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  exact Affine.UnramifiedFieldCriterion.specMap_formallyUnramified_of_fieldPullbacks φ h

theorem formallyUnramified_of_fieldPullbacks {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (h : ∀ (K : Type u) [Field K] (b : Spec (.of K) ⟶ Y),
      FormallyUnramified (pullback.snd f b)) : FormallyUnramified f := by
  have : IsZariskiLocalAtTarget (@FormallyUnramified : MorphismProperty Scheme.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtTarget _ RingHom.FormallyUnramified inferInstance
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := (@FormallyUnramified : MorphismProperty Scheme.{u})) Y.affineCover]
  intro i
  have ht : LocallyOfFiniteType (pullback.snd f (Y.affineCover.f i)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (IsPullback.of_hasPullback f (Y.affineCover.f i)) inferInstance
  refine @formallyUnramified_of_fieldPullbacks_affineTarget _ _
    (pullback.snd f (Y.affineCover.f i)) ht ?_
  intro K _ b
  have := h K (b ≫ Y.affineCover.f i)
  exact UnramifiedPullbackRefinements.unramified_iterated_pullback f (Y.affineCover.f i) b

theorem formallyUnramified_iff_fieldPullbacks {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] :
    FormallyUnramified f ↔ ∀ (K : Type u) [Field K] (b : Spec (.of K) ⟶ Y),
      FormallyUnramified (pullback.snd f b) := by
  constructor
  · intro hf K _ b
    exact MorphismProperty.of_isPullback (P := @FormallyUnramified) (IsPullback.of_hasPullback f b) hf
  · exact formallyUnramified_of_fieldPullbacks f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeUnramifiedFieldCriterion

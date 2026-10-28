import OAI.ArithmeticGeometry.Models.SpreadingOut.Base

/-! # Smooth Shrink -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothShrink.Construction

noncomputable section

/-! Removing the finite smoothness obstruction from an existing proper model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- An open contained in the smooth locus is smooth over the base. -/
theorem smooth_on_open_in_smoothLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (U : X.Opens) (hU : U ≤ f.smoothLocus) : Smooth (U.ι ≫ f) := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  apply top_unique
  intro x _
  exact hU x.property

/-- If a proper, finitely presented model is smooth at every point above the
generic point, its nonsmooth fibers disappear after deleting finitely many
primes. This lemma does not assume the existence of a smooth proper model. -/
theorem proper_model_smooth_after_shrinking
    {R : Type u} [CommRing R] [IsDomain R] [Ring.HasFiniteQuotients R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [LocallyOfFinitePresentation f]
    (hgeneric : ∀ x, f x = (show PrimeSpectrum R from ⊥) → x ∈ f.smoothLocus) :
    ∃ U : (Spec (CommRingCat.of R)).Opens,
      ((U : Set (Spec (CommRingCat.of R)))ᶜ).Finite ∧
      (show PrimeSpectrum R from ⊥) ∈ U ∧
      Smooth (f ∣_ U) ∧ IsProper (f ∣_ U) := by
  classical
  let Z : Set (Spec (CommRingCat.of R)) := f '' (f.smoothLocus : Set X)ᶜ
  have hZ : IsClosed Z := f.isClosedMap _ f.smoothLocus.isOpen.isClosed_compl
  have hη : (show PrimeSpectrum R from ⊥) ∉ Z := by
    rintro ⟨x, hx, heq⟩
    exact hx (hgeneric x heq)
  let U : (Spec (CommRingCat.of R)).Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  have hpre : f ⁻¹ᵁ U ≤ f.smoothLocus := by
    intro x hx
    by_contra hn
    exact hx ⟨x, hn, rfl⟩
  have hs : Smooth ((f ⁻¹ᵁ U).ι ≫ f) :=
    smooth_on_open_in_smoothLocus f _ hpre
  have hscomp : Smooth ((f ∣_ U) ≫ U.ι) := by
    rw [morphismRestrict_ι]
    exact hs
  refine ⟨U, ?_, hη, ?_, inferInstance⟩
  · change (Zᶜᶜ).Finite
    rw [compl_compl]
    change Set.Finite (α := PrimeSpectrum R) Z
    exact Fg.Construction.finite_closed_away_generic Z hZ hη
  · have hpb : IsPullback (𝟙 (f ⁻¹ᵁ U).toScheme) (f ∣_ U)
        ((f ∣_ U) ≫ U.ι) U.ι :=
      IsPullback.of_horiz_isIso_mono ⟨by simp⟩
    exact MorphismProperty.of_isPullback hpb hscomp

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothShrink.Construction

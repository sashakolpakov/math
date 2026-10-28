import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.BaseOpen
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Birational

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.BaseChange.Construction

noncomputable section

/-! Scheme-theoretic localization compatibility of the affine blowup for Blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- A proper scheme mapping by an open immersion into an integral separated
scheme over an open base is the entire base change. -/
theorem isPullback_of_proper_open_diagram
    {X X' Y Y' : Scheme.{u}} [IsIntegral X] [Nonempty X']
    (f : X ⟶ Y) [IsSeparated f]
    (j : Y' ⟶ Y) [IsOpenImmersion j]
    (f' : X' ⟶ Y') [IsProper f']
    (i : X' ⟶ X) [IsOpenImmersion i] (h : i ≫ f = f' ≫ j) :
    IsPullback i f' f j := by
  let t : X' ⟶ Limits.pullback f j := Limits.pullback.lift i f' h
  have ht₁ : t ≫ Limits.pullback.fst f j = i := Limits.pullback.lift_fst _ _ _
  have ht₂ : t ≫ Limits.pullback.snd f j = f' := Limits.pullback.lift_snd _ _ _
  let : Nonempty (Limits.pullback f j : Scheme.{u}) :=
    Nonempty.map (fun x : X' => t x) inferInstance
  let : IsIntegral (Limits.pullback f j) :=
    isIntegral_of_isOpenImmersion (Limits.pullback.fst f j)
  let : IsOpenImmersion (t ≫ Limits.pullback.fst f j) := ht₁.symm ▸ inferInstance
  let : IsOpenImmersion t := IsOpenImmersion.of_comp t (Limits.pullback.fst f j)
  let : IsProper (t ≫ Limits.pullback.snd f j) := ht₂.symm ▸ inferInstance
  let : IsProper t := IsProper.of_comp t (Limits.pullback.snd f j)
  have hdense : Dense (t.opensRange : Set (Limits.pullback f j : Scheme.{u})) :=
    t.opensRange.isOpen.dense (Set.range_nonempty t)
  have hclosed : IsClosed (Set.range t) := t.isClosedMap.isClosed_range
  have hrange : t.opensRange = ⊤ := by
    apply TopologicalSpace.Opens.ext
    change Set.range t = Set.univ
    rw [← hclosed.closure_eq]
    exact hdense.closure_eq
  let : IsIso t := isIso_of_isOpenImmersion_of_opensRange_eq_top t hrange
  exact IsPullback.of_iso_pullback ⟨h⟩ (asIso t) ht₁ ht₂

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (I : Ideal R) (s : R) [IsLocalization.Away s S]

/-- Blowup of a nonzero ideal in an affine Noetherian integral scheme
commutes with localization at a nonzero base element. -/
theorem affineBlowup_localization_isPullback
    [IsDomain R] [IsNoetherianRing R] (hI : I ≠ ⊥) (hs : s ≠ 0) :
    IsPullback (ReesMap.Construction.affineBlowupMap I (algebraMap R S))
      (ReesGrading.Construction.affineBlowupToSpec (I.map (algebraMap R S)))
      (ReesGrading.Construction.affineBlowupToSpec I) (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have hRS : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
  have hIS : I.map (algebraMap R S) ≠ ⊥ := by
    intro hzero
    obtain ⟨r, hr, hr0⟩ := (Submodule.ne_bot_iff I).mp hI
    have hm := Ideal.mem_map_of_mem (algebraMap R S) hr
    rw [hzero] at hm
    exact hr0 (hRS (by simpa using Ideal.mem_bot.mp hm))
  let : IsDomain S := IsLocalization.Away.isDomain S hs
  let : IsNoetherianRing S :=
    IsLocalization.isNoetherianRing (Submonoid.powers s) S inferInstance
  let : IsIntegral (ReesGrading.Construction.affineBlowup I) := Cover.Construction.affineBlowup_integral I hI
  let : IsIntegral (ReesGrading.Construction.affineBlowup (I.map (algebraMap R S))) :=
    Cover.Construction.affineBlowup_integral (I.map (algebraMap R S)) hIS
  let : IsOpenImmersion (ReesMap.Construction.affineBlowupMap I (algebraMap R S)) :=
    BaseOpen.Construction.affineBlowupMap_isOpenImmersion I s hs
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    IsOpenImmersion.of_isLocalization s
  exact isPullback_of_proper_open_diagram (ReesGrading.Construction.affineBlowupToSpec I)
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (ReesGrading.Construction.affineBlowupToSpec (I.map (algebraMap R S)))
    (ReesMap.Construction.affineBlowupMap I (algebraMap R S)) (BaseOpen.Construction.affineBlowupMap_over I (algebraMap R S))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.BaseChange.Construction

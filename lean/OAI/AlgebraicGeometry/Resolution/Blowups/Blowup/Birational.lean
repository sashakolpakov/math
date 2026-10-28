import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Cover
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Localization
import Mathlib.AlgebraicGeometry.Birational.Birational

/-! # Birational -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Birational.Construction

noncomputable section

/-! Birationality and the complement comparison for the actual affine blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- A common nonempty open scheme identifies dense opens of two irreducible
schemes, compatibly with a specified morphism between them. -/
theorem compatible_partialIso_of_common_open
    {U X Y : Scheme.{u}} [Nonempty U] [IrreducibleSpace X] [IrreducibleSpace Y]
    (i : U ⟶ X) (j : U ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    (f : X ⟶ Y) (h : i ≫ f = j) :
    ∃ e : X.PartialIso Y,
      e.source.ι ≫ f = e.iso.hom ≫ e.target.ι := by
  have hi : Dense (i.opensRange : Set X) :=
    i.opensRange.isOpen.dense (Set.range_nonempty i)
  have hj : Dense (j.opensRange : Set Y) :=
    j.opensRange.isOpen.dense (Set.range_nonempty j)
  refine ⟨{
    source := i.opensRange
    dense_source := hi
    target := j.opensRange
    dense_target := hj
    iso := i.isoOpensRange.symm ≪≫ j.isoOpensRange
  }, ?_⟩
  change i.opensRange.ι ≫ f =
    (i.isoOpensRange.inv ≫ j.isoOpensRange.hom) ≫ j.opensRange.ι
  rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, ← h,
    ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The affine blowup of a nonzero ideal of a domain is birational by a
partial isomorphism compatible with its actual structural morphism. -/
theorem affineBlowup_partialIso [IsDomain R] (hI : I ≠ ⊥) :
    ∃ e : (ReesGrading.Construction.affineBlowup I).PartialIso (Spec (.of R)),
      e.source.ι ≫ ReesGrading.Construction.affineBlowupToSpec I = e.iso.hom ≫ e.target.ι := by
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff I).mp hI
  let aI : I := ⟨a, ha⟩
  let : IsDomain (Localization.Away a) := Localization.Away.isDomain ha0
  let : IrreducibleSpace (ReesGrading.Construction.affineBlowup I) := Cover.Construction.affineBlowup_irreducible I hI
  exact compatible_partialIso_of_common_open
    (Blowup.Localization.Construction.affineBlowupComplementMap I aI) (Blowup.Localization.Construction.baseLocalizationMap a)
    (ReesGrading.Construction.affineBlowupToSpec I) (Blowup.Localization.Construction.affineBlowupComplementMap_over I aI)

/-- In particular the affine blowup and its integral affine base are birational. -/
theorem affineBlowup_birational [IsDomain R] (hI : I ≠ ⊥) :
    Scheme.Birational (ReesGrading.Construction.affineBlowup I) (Spec (.of R)) := by
  obtain ⟨e, _⟩ := affineBlowup_partialIso I hI
  exact ⟨e⟩

/-- An open section over an open subscheme exhausts the corresponding base
change of a separated morphism whose source is integral. -/
theorem isIso_pullback_snd_of_open_section
    {U X Y : Scheme.{u}} [Nonempty U] [IsIntegral X]
    (f : X ⟶ Y) [IsSeparated f]
    (j : U ⟶ Y) [IsOpenImmersion j]
    (i : U ⟶ X) [IsOpenImmersion i] (h : i ≫ f = j) :
    IsIso (Limits.pullback.snd f j) := by
  let s : U ⟶ Limits.pullback f j :=
    Limits.pullback.lift i (𝟙 U) (by simpa using h)
  have hs₁ : s ≫ Limits.pullback.fst f j = i := Limits.pullback.lift_fst _ _ _
  have hs₂ : s ≫ Limits.pullback.snd f j = 𝟙 U := Limits.pullback.lift_snd _ _ _
  let : Nonempty (Limits.pullback f j : Scheme.{u}) :=
    Nonempty.map (fun x : U => s x) inferInstance
  let : IsIntegral (Limits.pullback f j) :=
    isIntegral_of_isOpenImmersion (Limits.pullback.fst f j)
  let : IsOpenImmersion (s ≫ Limits.pullback.fst f j) := hs₁.symm ▸ inferInstance
  let : IsOpenImmersion s := IsOpenImmersion.of_comp s (Limits.pullback.fst f j)
  let : IsClosedImmersion (s ≫ Limits.pullback.snd f j) := hs₂.symm ▸ inferInstance
  let : IsClosedImmersion s := IsClosedImmersion.of_comp s (Limits.pullback.snd f j)
  have hdense : Dense (s.opensRange : Set (Limits.pullback f j : Scheme.{u})) :=
    s.opensRange.isOpen.dense (Set.range_nonempty s)
  have hclosed : IsClosed (Set.range s) := s.isClosedEmbedding.isClosed_range
  have hrange : s.opensRange = ⊤ := by
    apply TopologicalSpace.Opens.ext
    change Set.range s = Set.univ
    rw [← hclosed.closure_eq]
    exact hdense.closure_eq
  let : IsIso s := isIso_of_isOpenImmersion_of_opensRange_eq_top s hrange
  let : IsIso (s ≫ Limits.pullback.snd f j) := hs₂.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_left s (Limits.pullback.snd f j)

/-- The blowup is an isomorphism after localizing at a nonzero element of
the center ideal, hence away from the center on this basic open. -/
theorem affineBlowup_localization_isIso [IsDomain R] [IsNoetherianRing R]
    (a : I) (ha : a.val ≠ 0) :
    IsIso (Limits.pullback.snd (ReesGrading.Construction.affineBlowupToSpec I) (Blowup.Localization.Construction.baseLocalizationMap a.val)) := by
  have hI : I ≠ ⊥ := by
    intro hI
    have : a.val ∈ (⊥ : Ideal R) := hI ▸ a.property
    exact ha (Ideal.mem_bot.mp this)
  let : IsIntegral (ReesGrading.Construction.affineBlowup I) := Cover.Construction.affineBlowup_integral I hI
  let : IsDomain (Localization.Away a.val) := Localization.Away.isDomain ha
  exact isIso_pullback_snd_of_open_section (ReesGrading.Construction.affineBlowupToSpec I)
    (Blowup.Localization.Construction.baseLocalizationMap a.val) (Blowup.Localization.Construction.affineBlowupComplementMap I a)
    (Blowup.Localization.Construction.affineBlowupComplementMap_over I a)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Birational.Construction

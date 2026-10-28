import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Data
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Complement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Complement.Construction

noncomputable section

/-! Isomorphism of the global blowup away from its center. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- Isomorphisms on smaller open neighborhoods imply an isomorphism on the
open subset they cover. -/
theorem isIso_restrict_of_local_restrictions
    {X Y : Scheme.{u}} (f : X ⟶ Y) (O : Y.Opens)
    (H : ∀ y : Y, y ∈ O → ∃ V : Y.Opens, y ∈ V ∧ V ≤ O ∧ IsIso (f ∣_ V)) :
    IsIso (f ∣_ O) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
  intro y
  obtain ⟨V, hy, hVO, hfV⟩ := H y.1 y.2
  let W : O.toScheme.Opens := O.ι ⁻¹ᵁ V
  have himage : O.ι ''ᵁ W = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVO]
  refine ⟨W, hy, ?_⟩
  apply ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f O W)).mpr
  change IsIso (f ∣_ O.ι ''ᵁ W)
  rw [himage]
  exact hfV

/-- An isomorphism over an open subset remains an isomorphism over a smaller open. -/
theorem isIso_restrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y) {O V : Y.Opens}
    (hOV : O ≤ V) [IsIso (f ∣_ V)] : IsIso (f ∣_ O) := by
  let W : V.toScheme.Opens := V.ι ⁻¹ᵁ O
  have himage : V.ι ''ᵁ W = O := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hOV]
  have h := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f V W)).mp (inferInstance : IsIso (f ∣_ V ∣_ W))
  change IsIso (f ∣_ V.ι ''ᵁ W) at h
  rw [himage] at h
  exact h

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable (I : X.IdealSheafData) (hI : I ≠ ⊥)

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- The range of a localization of an affine chart is its basic open in the base. -/
theorem baseLocalization_fromSpec_range (U : X.affineOpens) (a : Γ(X, U)) :
    letI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    (Blowup.Localization.Construction.baseLocalizationMap a ≫ U.2.fromSpec).opensRange = X.basicOpen a := by
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  rw [Scheme.Hom.opensRange_comp]
  change U.2.fromSpec ''ᵁ
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away a)))).opensRange = _
  rw [Scheme.Hom.opensRange_localizationAway, U.2.fromSpec_image_basicOpen]

/-- The blowup restricts to an isomorphism on each basic open defined by a
nonzero section of the center ideal. -/
theorem globalBlowup_basicOpen_isIso (U : X.affineOpens) [Nonempty U.1]
    (a : I.ideal U) (ha : a.val ≠ 0) :
    IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ∣_ X.basicOpen a.val) := by
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let j := Blowup.Localization.Construction.baseLocalizationMap a.val ≫ U.2.fromSpec
  let : IsOpenImmersion j := inferInstance
  have hj : IsIso (pullback.snd (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) j) :=
    GlobalBlowup.Data.Construction.globalBlowup_localization_isIso I hI U a ha
  have h := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictOpensRange (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) j)).mpr hj
  change IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ∣_ j.opensRange) at h
  have hrange : j.opensRange = X.basicOpen a.val := baseLocalization_fromSpec_range U a.val
  rw [hrange] at h
  exact h

/-- The global blowup is an isomorphism over the entire complement of the
closed center defined by its ideal sheaf. -/
theorem globalBlowup_supportComplement_isIso :
    IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ∣_ I.support.compl) := by
  apply isIso_restrict_of_local_restrictions
  intro x hx
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  let V : X.affineOpens := ⟨U, hU⟩
  let : Nonempty V.1 := ⟨⟨x, hxU⟩⟩
  have hnot : x ∉ X.zeroLocus (U := V.1) (I.ideal V) := by
    intro hz
    exact hx ((Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) hxU).mpr hz)
  simp only [Scheme.mem_zeroLocus_iff, not_forall, Classical.not_not] at hnot
  obtain ⟨a, ha, hxa⟩ := hnot
  have ha0 : a ≠ 0 := by
    intro ha0
    rw [ha0, Scheme.basicOpen_zero] at hxa
    exact hxa
  refine ⟨X.basicOpen a, hxa, ?_, globalBlowup_basicOpen_isIso I hI V ⟨a, ha⟩ ha0⟩
  intro y hy
  change y ∉ I.support
  intro hys
  have hz := (Scheme.IdealSheafData.mem_support_iff.mp hys) V
  exact ((Scheme.mem_zeroLocus_iff X _ _).mp hz) a ha hy

/-- Any open subset disjoint from the center is preserved by the blowup. -/
theorem globalBlowup_isIso_on_open (O : X.Opens) (hO : O ≤ I.support.compl) :
    IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ∣_ O) := by
  let : IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ∣_ I.support.compl) :=
    globalBlowup_supportComplement_isIso I hI
  exact isIso_restrict_of_le (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) hO

/-- A blowup whose center is contained in the singular locus preserves the
smooth locus of the given structural morphism. -/
theorem globalBlowup_preserves_smoothLocus {S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f]
    (hcenter : (I.support : Set X) ⊆ (f.smoothLocus : Set X)ᶜ) :
    IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ∣_ f.smoothLocus) := by
  apply globalBlowup_isIso_on_open I hI
  intro x hx
  exact fun hxs => hcenter hxs hx

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Complement.Construction

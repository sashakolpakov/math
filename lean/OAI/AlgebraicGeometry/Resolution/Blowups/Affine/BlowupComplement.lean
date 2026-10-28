import OAI.AlgebraicGeometry.Resolution.Blowups.PrincipalBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.FlatBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Complement

/-! # Blowup Complement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupComplement.Construction

noncomputable section

/-! The actual affine blowup is an isomorphism off its center, without
domain or nonzero-ideal assumptions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R]

theorem affineBlowupToSpec_unitIdeal_isIso :
    IsIso (ReesGrading.Construction.affineBlowupToSpec (⊤ : Ideal R)) := by
  apply PrincipalBlowup.Construction.affineBlowupToSpec_isIso_of_principal (⊤ : Ideal R) ⟨1, trivial⟩
  · exact (Ideal.span_singleton_one : Ideal.span {(1 : R)} = ⊤).symm
  · exact isRegular_one

theorem affineBlowup_localized_structure_isIso (I : Ideal R) (g : R) (hg : g ∈ I) :
    IsIso (ReesGrading.Construction.affineBlowupToSpec (I.map (algebraMap R (Localization.Away g)))) := by
  have hmap : I.map (algebraMap R (Localization.Away g)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hg)
      (IsLocalization.Away.algebraMap_isUnit g)
  rw [hmap]
  exact affineBlowupToSpec_unitIdeal_isIso

theorem isIso_pullback_snd_of_isPullback
    {X' X Y' Y : Scheme.{u}} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (j : Y' ⟶ Y)
    (hpb : IsPullback i f' f j) [IsIso f'] : IsIso (pullback.snd f j) := by
  let : IsIso (hpb.isoPullback.hom ≫ pullback.snd f j) := hpb.isoPullback_hom_snd.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_left hpb.isoPullback.hom _

theorem affineBlowup_localization_pullback_isIso (I : Ideal R) (g : R) (hg : g ∈ I) :
    IsIso (pullback.snd (ReesGrading.Construction.affineBlowupToSpec I)
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g))))) := by
  let : IsIso (ReesGrading.Construction.affineBlowupToSpec (I.map (algebraMap R (Localization.Away g)))) :=
    affineBlowup_localized_structure_isIso I g hg
  exact isIso_pullback_snd_of_isPullback _ _ _ _
    (Blowup.FlatBaseChange.Construction.affineBlowup_flat_isPullback (S := Localization.Away g) I)

theorem isIso_restrict_opensRange_of_pullback_snd
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (j : Y' ⟶ Y) [IsOpenImmersion j]
    [IsIso (pullback.snd f j)] : IsIso (f ∣_ j.opensRange) := by
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictOpensRange f j)).mpr (inferInstance : IsIso (pullback.snd f j))

/-- On every basic open cut out by an element of the center ideal,
the actual blowup is an isomorphism. -/
theorem affineBlowup_basicOpen_isIso (I : Ideal R) (g : R) (hg : g ∈ I) :
    IsIso (ReesGrading.Construction.affineBlowupToSpec I ∣_ PrimeSpectrum.basicOpen g) := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))
  let : IsOpenImmersion j := IsOpenImmersion.of_isLocalization g
  let : IsIso (pullback.snd (ReesGrading.Construction.affineBlowupToSpec I) j) :=
    affineBlowup_localization_pullback_isIso I g hg
  have h := isIso_restrict_opensRange_of_pullback_snd (ReesGrading.Construction.affineBlowupToSpec I) j
  have hrange : j.opensRange = PrimeSpectrum.basicOpen g :=
    Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of R) g
  rw [hrange] at h
  exact h

/-- The complement of the actual affine closed center. -/
def affineCenterComplement (I : Ideal R) : (Spec (CommRingCat.of R)).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (I : Set R))ᶜ, (PrimeSpectrum.isClosed_zeroLocus (I : Set R)).isOpen_compl⟩

/-- The entire complement of the center is unchanged by the blowup. -/
theorem affineBlowup_centerComplement_isIso (I : Ideal R) :
    IsIso (ReesGrading.Construction.affineBlowupToSpec I ∣_ affineCenterComplement I) := by
  apply Blowup.Complement.Construction.isIso_restrict_of_local_restrictions
  intro q hq
  have hn : ¬ I ≤ q.asIdeal := hq
  obtain ⟨g, hgI, hgq⟩ := SetLike.not_le_iff_exists.mp hn
  refine ⟨PrimeSpectrum.basicOpen g, hgq, ?_, affineBlowup_basicOpen_isIso I g hgI⟩
  intro p hp
  change ¬ I ≤ p.asIdeal
  intro hIp
  exact hp (hIp hgI)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupComplement.Construction

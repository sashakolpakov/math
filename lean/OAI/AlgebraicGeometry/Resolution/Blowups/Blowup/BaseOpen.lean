import OAI.AlgebraicGeometry.Resolution.Blowups.HomogeneousLocalization
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Base Open -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.BaseOpen.Construction

noncomputable section

/-! Open restriction maps for the affine blowup construction in Blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Open immersions on the homogeneous affine charts give an open immersion
of the projective spectra. -/
theorem projMap_isOpenImmersion_of_awayMaps
    {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (g : 𝒜 →+*ᵍ ℬ)
    (hrel : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g)
    (haway : ∀ (d : ℕ), 0 < d → ∀ (f : A), f ∈ 𝒜 d →
      IsOpenImmersion (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map g f)))) :
    IsOpenImmersion (Proj.map g hrel) := by
  apply IsZariskiLocalAtTarget.of_openCover (Proj.affineOpenCover 𝒜).openCover
  intro a
  change (Σ n : PNat, 𝒜 (n : ℕ)) at a
  rcases a with ⟨⟨d, hd⟩, f, hf⟩
  change f ∈ 𝒜 d at hf
  change IsOpenImmersion (Limits.pullback.snd (Proj.map g hrel)
    (Proj.awayι 𝒜 f hf hd))
  let : IsOpenImmersion (Proj.awayι 𝒜 f hf hd) := by
    unfold Proj.awayι
    infer_instance
  let : IsOpenImmersion
      (Proj.awayι ℬ (g f) (g.map_mem hf) hd) := by
    unfold Proj.awayι
    infer_instance
  have hpb : IsPullback
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map g f)))
      (Proj.awayι ℬ (g f) (g.map_mem hf) hd)
      (Proj.awayι 𝒜 f hf hd) (Proj.map g hrel) := by
    apply IsOpenImmersion.isPullback
    · exact Proj.awayι_comp_map g hrel hd f hf
    · rw [Proj.opensRange_awayι, Proj.opensRange_awayι, Proj.map_preimage_basicOpen]
  let : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map g f))) :=
    haway d hd f hf
  rw [← hpb.flip.isoPullback_inv_snd]
  infer_instance

/-- The projective-spectrum morphism commutes with its degree-zero base map. -/
theorem projMap_toSpecZero
    {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (g : 𝒜 →+*ᵍ ℬ)
    (hrel : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    Proj.map g hrel ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom g.gradedZeroRingHom) := by
  refine (Proj.mapAffineOpenCover g hrel).openCover.hom_ext _ _ (fun a => ?_)
  change (Σ n : PNat, 𝒜 (n : ℕ)) at a
  rcases a with ⟨⟨d, hd⟩, f, hf⟩
  change f ∈ 𝒜 d at hf
  change Proj.awayι ℬ (g f) (g.map_mem hf) hd ≫ (Proj.map g hrel ≫ Proj.toSpecZero 𝒜) =
    Proj.awayι ℬ (g f) (g.map_mem hf) hd ≫
      (Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom g.gradedZeroRingHom))
  simp only [← Category.assoc]
  rw [Proj.awayι_comp_map g hrel hd f hf, Category.assoc, Proj.awayι_toSpecZero, Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact Blowups.HomogeneousLocalization.Construction.homogeneousAway_map_fromZero g f x

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (I : Ideal R) (s : R) [IsLocalization.Away s S]

/-- On each homogeneous chart, base localization induces an open immersion. -/
theorem reesAwayMap_isOpenImmersion [IsDomain R] (hs : s ≠ 0)
    {f : reesAlgebra I} {d : ℕ} (hf : f ∈ ReesGrading.Construction.reesGrade I d) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (HomogeneousLocalization.Away.map (ReesMap.Construction.reesGradedMap I (algebraMap R S)) f))) := by
  let : Algebra (HomogeneousLocalization.Away (ReesGrading.Construction.reesGrade I) f)
      (HomogeneousLocalization.Away (ReesGrading.Construction.reesGrade (I.map (algebraMap R S)))
        (ReesMap.Construction.reesGradedMap I (algebraMap R S) f)) :=
    (HomogeneousLocalization.Away.map (ReesMap.Construction.reesGradedMap I (algebraMap R S)) f).toAlgebra
  let x : HomogeneousLocalization.Away (ReesGrading.Construction.reesGrade I) f :=
    HomogeneousLocalization.fromZeroRingHom (ReesGrading.Construction.reesGrade I) (Submonoid.powers f)
      ⟨algebraMap R (reesAlgebra I) s, SetLike.algebraMap_mem_graded (ReesGrading.Construction.reesGrade I) s⟩
  let : IsLocalization.Away x
      (HomogeneousLocalization.Away (ReesGrading.Construction.reesGrade (I.map (algebraMap R S)))
        (ReesMap.Construction.reesGradedMap I (algebraMap R S) f)) := Blowups.HomogeneousLocalization.Construction.reesAwayMap_isLocalization I s hs hf
  exact IsOpenImmersion.of_isLocalization x

/-- Localizing the base of an affine blowup induces an open immersion of
the actual blowup schemes. -/
theorem affineBlowupMap_isOpenImmersion [IsDomain R] (hs : s ≠ 0) :
    IsOpenImmersion (ReesMap.Construction.affineBlowupMap I (algebraMap R S)) := by
  apply projMap_isOpenImmersion_of_awayMaps
  intro d _ f hf
  exact reesAwayMap_isOpenImmersion I s hs hf

omit [Algebra R S] in
/-- The affine blowup morphism induced by a coefficient map lies over that
map of affine bases. -/
theorem affineBlowupMap_over (φ : R →+* S) :
    ReesMap.Construction.affineBlowupMap I φ ≫ ReesGrading.Construction.affineBlowupToSpec I =
      ReesGrading.Construction.affineBlowupToSpec (I.map φ) ≫ Spec.map (CommRingCat.ofHom φ) := by
  unfold ReesMap.Construction.affineBlowupMap ReesGrading.Construction.affineBlowupToSpec
  rw [← Category.assoc, projMap_toSpecZero, Category.assoc, ← Spec.map_comp,
    Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  apply Subtype.ext
  exact ReesMap.Construction.reesRingMap_constants I φ r

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.BaseOpen.Construction

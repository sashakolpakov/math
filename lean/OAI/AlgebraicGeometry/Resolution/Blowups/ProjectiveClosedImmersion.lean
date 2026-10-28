import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.BaseOpen
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Projective Closed Immersion -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveClosedImmersion.Construction

noncomputable section

/-! Closed projective-spectrum maps for the projective blowup construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
variable [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
variable (g : 𝒜 →+*ᵍ ℬ)

/-- A homogeneous element has a homogeneous lift along a surjective graded map. -/
theorem gradedMap_homogeneous_surjective (hg : Function.Surjective g)
    (n : ℕ) (b : B) (hb : b ∈ ℬ n) :
    ∃ a : A, a ∈ 𝒜 n ∧ g a = b := by
  obtain ⟨a, rfl⟩ := hg b
  refine ⟨DirectSum.decompose 𝒜 a n, (DirectSum.decompose 𝒜 a n).property, ?_⟩
  rw [GradedRingHom.map_directSumDecompose, DirectSum.decompose_of_mem _ hb]
  simp

/-- A surjective graded map induces a surjective map on every homogeneous
localization chart. -/
theorem homogeneousAway_map_surjective (hg : Function.Surjective g)
    {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) :
    Function.Surjective (HomogeneousLocalization.Away.map g f) := by
  intro x
  obtain ⟨n, b, hb, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective ℬ (g.map_mem hf) x
  obtain ⟨a, ha, hga⟩ := gradedMap_homogeneous_surjective g hg (n • d) b hb
  refine ⟨HomogeneousLocalization.Away.mk 𝒜 hf n a ha, ?_⟩
  simp only [HomogeneousLocalization.Away.map_mk, hga]

/-- Surjectivity makes the projective-spectrum map defined everywhere. -/
theorem gradedMap_irrelevant_le_of_surjective (hg : Function.Surjective g) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g := by
  change (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g
  rw [HomogeneousIdeal.irrelevant_eq_span]
  apply Ideal.span_le.mpr
  intro b hb
  obtain ⟨n, hn, hb⟩ := (by simpa only [Set.mem_iUnion, SetLike.mem_coe] using hb)
  obtain ⟨a, ha, rfl⟩ := gradedMap_homogeneous_surjective g hg n b hb
  exact Ideal.mem_map_of_mem g (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn ha)

/-- Surjectivity of a graded map gives a closed immersion of its projective spectra. -/
theorem projMap_isClosedImmersion_of_surjective
    (hrel : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g)
    (hg : Function.Surjective g) : IsClosedImmersion (Proj.map g hrel) := by
  apply IsZariskiLocalAtTarget.of_openCover (Proj.affineOpenCover 𝒜).openCover
  intro a
  change (Σ n : PNat, 𝒜 (n : ℕ)) at a
  rcases a with ⟨⟨d, hd⟩, f, hf⟩
  change f ∈ 𝒜 d at hf
  change IsClosedImmersion (CategoryTheory.Limits.pullback.snd (Proj.map g hrel)
    (Proj.awayι 𝒜 f hf hd))
  let : IsOpenImmersion (Proj.awayι 𝒜 f hf hd) := by
    unfold Proj.awayι
    infer_instance
  let : IsOpenImmersion (Proj.awayι ℬ (g f) (g.map_mem hf) hd) := by
    unfold Proj.awayι
    infer_instance
  have hpb : IsPullback
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map g f)))
      (Proj.awayι ℬ (g f) (g.map_mem hf) hd)
      (Proj.awayι 𝒜 f hf hd) (Proj.map g hrel) := by
    apply IsOpenImmersion.isPullback
    · exact Proj.awayι_comp_map g hrel hd f hf
    · rw [Proj.opensRange_awayι, Proj.opensRange_awayι, Proj.map_preimage_basicOpen]
  let φ : CommRingCat.of (HomogeneousLocalization.Away 𝒜 f) ⟶
      CommRingCat.of (HomogeneousLocalization.Away ℬ (g f)) :=
    CommRingCat.ofHom (HomogeneousLocalization.Away.map g f)
  let : IsClosedImmersion (Spec.map φ) :=
    IsClosedImmersion.spec_of_surjective φ (homogeneousAway_map_surjective g hg hf)
  rw [← hpb.flip.isoPullback_inv_snd]
  infer_instance

/-- The closed projective-spectrum map associated to a surjective graded map. -/
def projClosedMap (hg : Function.Surjective g) : Proj ℬ ⟶ Proj 𝒜 :=
  Proj.map g (gradedMap_irrelevant_le_of_surjective g hg)

instance projClosedMap_isClosedImmersion (hg : Function.Surjective g) :
    IsClosedImmersion (projClosedMap g hg) :=
  projMap_isClosedImmersion_of_surjective g (gradedMap_irrelevant_le_of_surjective g hg) hg

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveClosedImmersion.Construction

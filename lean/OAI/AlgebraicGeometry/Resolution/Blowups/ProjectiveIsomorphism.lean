import OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveClosedImmersion

/-! # Projective Isomorphism -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveIsomorphism.Construction

noncomputable section

/-! Isomorphisms of projective spectra from bijective graded ring maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
variable [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The inverse of a bijective graded map preserves the actual homogeneous pieces. -/
def gradedMapInverse (g : 𝒜 →+*ᵍ ℬ) (hg : Function.Bijective g) : ℬ →+*ᵍ 𝒜 where
  __ := (RingEquiv.ofBijective g.toRingHom hg).symm.toRingHom
  map_mem {n} {b} hb := by
    obtain ⟨a, ha, rfl⟩ := ProjectiveClosedImmersion.Construction.gradedMap_homogeneous_surjective g hg.2 n b hb
    change (RingEquiv.ofBijective g.toRingHom hg).symm
      ((RingEquiv.ofBijective g.toRingHom hg) a) ∈ 𝒜 n
    simpa only [RingEquiv.symm_apply_apply] using ha

theorem gradedMapInverse_surjective (g : 𝒜 →+*ᵍ ℬ) (hg : Function.Bijective g) :
    Function.Surjective (gradedMapInverse g hg) :=
  (RingEquiv.ofBijective g.toRingHom hg).symm.surjective

/-- A bijective graded map induces an isomorphism of the actual schemes. -/
theorem projMap_isIso_of_bijective (g : 𝒜 →+*ᵍ ℬ)
    (hrel : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g)
    (hg : Function.Bijective g) : IsIso (Proj.map g hrel) := by
  let h := gradedMapInverse g hg
  have hh := ProjectiveClosedImmersion.Construction.gradedMap_irrelevant_le_of_surjective h (gradedMapInverse_surjective g hg)
  have h₁ : h.comp g = GradedRingHom.id 𝒜 := by
    ext a
    exact (RingEquiv.ofBijective g.toRingHom hg).symm_apply_apply a
  have h₂ : g.comp h = GradedRingHom.id ℬ := by
    ext b
    exact (RingEquiv.ofBijective g.toRingHom hg).apply_symm_apply b
  refine ⟨⟨Proj.map h hh, ?_, ?_⟩⟩
  · rw [← Proj.map_comp]
    simp only [h₂, Proj.map_id]
  · rw [← Proj.map_comp]
    simp only [h₁, Proj.map_id]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveIsomorphism.Construction

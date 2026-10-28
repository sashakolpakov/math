import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapBase

/-! # Surjective Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.SurjectiveChart.BundleCycles

noncomputable section

/-! Surjective graded ring maps induce surjective maps of the actual
homogeneous affine-chart rings. -/

open _root_.HomogeneousLocalization

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)

include hf in
theorem gradedSurjective_homogeneousPreimage (n : ℕ) (b : B) (hb : b ∈ ℬ n) :
    ∃ a : A, a ∈ 𝒜 n ∧ f a = b := by
  obtain ⟨a, rfl⟩ := hf b
  refine ⟨(DirectSum.decompose 𝒜 a n).val, (DirectSum.decompose 𝒜 a n).property, ?_⟩
  exact (GradedRingHom.map_directSumDecompose 𝒜 ℬ f).trans (DirectSum.decompose_of_mem_same ℬ hb)

include hf in
theorem gradedAwayMap_surjective {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) :
    Function.Surjective (Away.map f s) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (f.map_mem hs) z
  obtain ⟨a, ha, rfl⟩ := gradedSurjective_homogeneousPreimage f hf (n • k) b hb
  exact ⟨Away.mk 𝒜 hs n a ha, Away.map_mk f s hs n a ha⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.SurjectiveChart.BundleCycles

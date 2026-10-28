import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartMap

/-! # Chart Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ChartMap.BundleCycles

noncomputable section

/-! The actual projective map restricts to the homogeneous chart map
when its two coordinates correspond. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousLocalization

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (s : A) (t : B) (hst : f s = t)

theorem gradedChartMap_awayι {k : ℕ} (hk : 0 < k) (hs : s ∈ 𝒜 k) (ht : t ∈ ℬ k) :
    Spec.map (CommRingCat.ofHom (Graded.ChartMap.BundleCycles.gradedChartMap f s t hst)) ≫ Proj.awayι 𝒜 s hs hk =
      Proj.awayι ℬ t ht hk ≫ Proj.map f hf := by
  subst t
  exact (Proj.awayι_comp_map f hf hk s hs).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ChartMap.BundleCycles

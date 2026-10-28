import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapBase
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Map Chart Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapChartPullback.BundleCycles

noncomputable section

/-! Native affine-chart squares for the actual Proj map are pullbacks. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousLocalization

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)

theorem projectiveMap_chart_isPullback {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) (hk : 0 < k) :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map f s)))
      (Proj.awayι ℬ (f s) (f.map_mem hs) hk) (Proj.awayι 𝒜 s hs hk) (Proj.map f hf) := by
  apply IsOpenImmersion.isPullback
  · exact Proj.awayι_comp_map f hf hk s hs
  · rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
    exact Proj.map_preimage_basicOpen f hf s

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapChartPullback.BundleCycles

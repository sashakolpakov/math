import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapBase

/-! # Chart Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartMap.BundleCycles

noncomputable section

/-! Actual chart maps with a specified target homogeneous coordinate. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousLocalization

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (s : A) (t : B) (hst : f s = t)

def gradedChartMap : Away 𝒜 s →+* Away ℬ t :=
  HomogeneousLocalization.map f (by
    rintro a ⟨n, rfl⟩
    change f (s ^ n) ∈ Submonoid.powers t
    rw [map_pow, hst]
    exact ⟨n, rfl⟩)

theorem gradedChartMap_mk {k : ℕ} (hs : s ∈ 𝒜 k) (ht : t ∈ ℬ k)
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • k)) :
    gradedChartMap f s t hst (Away.mk 𝒜 hs n a ha) =
      Away.mk ℬ ht n (f a) (f.map_mem ha) := by
  unfold gradedChartMap Away.mk
  rw [HomogeneousLocalization.map_mk]
  apply HomogeneousLocalization.val_injective
  rw [val_mk, val_mk]
  exact congrArg (Localization.mk (f a)) (Subtype.ext (by
    change f (s ^ n) = t ^ n
    rw [map_pow, hst]))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartMap.BundleCycles

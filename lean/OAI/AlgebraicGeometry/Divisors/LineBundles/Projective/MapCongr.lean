import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # Map Congr -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapCongr.BundleCycles

noncomputable section

/-! Equality of actual graded homomorphisms identifies their Proj maps. -/

open _root_.AlgebraicGeometry

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

theorem projectiveMap_congr {f g : 𝒜 →+*ᵍ ℬ} (h : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    Proj.map f hf = Proj.map g hg := by
  subst g
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapCongr.BundleCycles

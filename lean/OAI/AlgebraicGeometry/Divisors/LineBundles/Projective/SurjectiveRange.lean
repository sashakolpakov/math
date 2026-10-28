import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ClosedImmersion
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.LocalizationRange

/-! # Surjective Range -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.SurjectiveRange.BundleCycles

noncomputable section

/-! The image of an actual projective map from a graded quotient is
the vanishing locus of its actual ring-theoretic kernel. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hsurj : Function.Surjective f)

include hsurj in
theorem projectiveSurjective_range :
    Set.range (Proj.map f hf) = ProjectiveSpectrum.zeroLocus 𝒜 (RingHom.ker f.toRingHom) := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩ a ha
    change f a ∈ q.asHomogeneousIdeal.toIdeal
    change f a = 0 at ha
    rw [ha]
    exact q.asHomogeneousIdeal.toIdeal.zero_mem
  · intro hp
    let p' : PrimeSpectrum A := ⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩
    have hrange : p' ∈ Set.range (PrimeSpectrum.comap f.toRingHom) := by
      rw [range_comap_of_surjective B f.toRingHom hsurj]
      exact hp
    obtain ⟨q, hq⟩ := hrange
    have hqI : q.asIdeal.comap f = p.asHomogeneousIdeal.toIdeal := congrArg PrimeSpectrum.asIdeal hq
    have hmap : (p.asHomogeneousIdeal.map f).toIdeal = q.asIdeal := by
      change Ideal.map f p.asHomogeneousIdeal.toIdeal = q.asIdeal
      rw [← hqI]
      exact Ideal.map_comap_of_surjective f hsurj q.asIdeal
    let qP : Proj ℬ :=
      { asHomogeneousIdeal := p.asHomogeneousIdeal.map f
        isPrime := hmap.symm ▸ q.isPrime
        not_irrelevant_le := by
          intro h
          have hl := (LocalizationRange.BundleCycles.gradedMap_irrelevant_le 𝒜 ℬ f).trans h
          have hc : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
              (p.asHomogeneousIdeal.map f).toIdeal.comap f := Ideal.map_le_iff_le_comap.mp hl
          rw [hmap, hqI] at hc
          exact p.not_irrelevant_le hc }
    refine ⟨qP, ?_⟩
    apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.ext
    exact (congrArg (Ideal.comap f) hmap).trans hqI

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.SurjectiveRange.BundleCycles

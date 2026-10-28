import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.PrincipalLocalization

/-! # Localization Range -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.LocalizationRange.BundleCycles

noncomputable section

/-! The image of the actual projective localization map is precisely
the nonvanishing open of its degree-zero denominator. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)

theorem gradedMap_irrelevant_le :
    (HomogeneousIdeal.irrelevant 𝒜).map f ≤ HomogeneousIdeal.irrelevant ℬ := by
  change Ideal.map f (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ (HomogeneousIdeal.irrelevant ℬ).toIdeal
  apply Ideal.map_le_iff_le_comap.mpr
  apply (HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr
  intro n hn a ha
  exact HomogeneousIdeal.mem_irrelevant_of_mem ℬ hn (f.map_mem ha)

theorem projectivePrincipalLocalization_range
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (r : A) (hlocal : letI := f.toRingHom.toAlgebra; IsLocalization.Away r B) :
    Set.range (Proj.map f hf) = Proj.basicOpen 𝒜 r := by
  let := f.toRingHom.toAlgebra
  let := hlocal
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    change f r ∉ q.asHomogeneousIdeal.toIdeal
    have hu : IsUnit (f r) := IsLocalization.map_units B ⟨r, Submonoid.mem_powers r⟩
    intro h
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  · intro hp
    let p' : PrimeSpectrum A := ⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩
    have hrange : p' ∈ Set.range (PrimeSpectrum.comap (algebraMap A B)) := by
      rw [PrimeSpectrum.localization_away_comap_range B r]
      exact hp
    obtain ⟨q, hq⟩ := hrange
    have hqI : q.asIdeal.comap f = p.asHomogeneousIdeal.toIdeal := congrArg PrimeSpectrum.asIdeal hq
    have hmap : (p.asHomogeneousIdeal.map f).toIdeal = q.asIdeal := by
      change Ideal.map f p.asHomogeneousIdeal.toIdeal = q.asIdeal
      rw [← hqI]
      exact IsLocalization.map_under (Submonoid.powers r) B q.asIdeal
    have hback : (p.asHomogeneousIdeal.map f).toIdeal.comap f = p.asHomogeneousIdeal.toIdeal :=
      (congrArg (Ideal.comap f) hmap).trans hqI
    let qP : Proj ℬ :=
      { asHomogeneousIdeal := p.asHomogeneousIdeal.map f
        isPrime := hmap.symm ▸ q.isPrime
        not_irrelevant_le := by
          intro h
          have hl := (gradedMap_irrelevant_le 𝒜 ℬ f).trans h
          have hc : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
              (p.asHomogeneousIdeal.map f).toIdeal.comap f := Ideal.map_le_iff_le_comap.mp hl
          rw [hback] at hc
          exact p.not_irrelevant_le hc }
    refine ⟨qP, ?_⟩
    apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.ext
    exact hback

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.LocalizationRange.BundleCycles

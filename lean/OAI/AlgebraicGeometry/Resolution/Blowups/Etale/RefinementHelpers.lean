import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.RefinementCoverage

/-! # Refinement Helpers -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RefinementHelpers.Construction

noncomputable section

/-! Smoothness and point coverage for actual étale refinement families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem smooth_target_of_etale_algHom (k : Type u) {R S : Type u}
    [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [Algebra.Smooth k R] (f : R →ₐ[k] S) (hf : f.toRingHom.Etale) : Algebra.Smooth k S := by
  let : Algebra R S := f.toRingHom.toAlgebra
  let : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  let : Algebra.Etale R S := RingHom.etale_algebraMap.mp hf
  exact Algebra.Smooth.comp k R S

/-- Commuting actual retraction maps lift a coefficient covering family
over the entire closed set defined by the original retraction kernel. -/
theorem retraction_square_cover_lifts {H R : Type u} [CommRing H] [CommRing R]
    {ι : Type u} (ρ : R →+* H) (hρ : Function.Surjective ρ)
    (B V : ι → CommRingCat.{u}) (φ : ∀ i, H →+* B i) (f : ∀ i, R →+* V i)
    (ρ' : ∀ i, V i →+* B i)
    (hcomm : ∀ i, (ρ' i).comp (f i) = (φ i).comp ρ)
    (hcover : ∀ p : PrimeSpectrum H, ∃ i, ∃ q : PrimeSpectrum (B i),
      PrimeSpectrum.comap (φ i) q = p)
    (p : PrimeSpectrum R) (hker : RingHom.ker ρ ≤ p.asIdeal) :
    ∃ i, ∃ q : PrimeSpectrum (V i), PrimeSpectrum.comap (f i) q = p := by
  let P : PrimeSpectrum H := ⟨p.asIdeal.map ρ, Ideal.map_isPrime_of_surjective hρ hker⟩
  have hP : P.asIdeal.comap ρ = p.asIdeal := by
    change (p.asIdeal.map ρ).comap ρ = p.asIdeal
    rw [Ideal.comap_map_of_surjective ρ hρ, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker]
  obtain ⟨i, q, hq⟩ := hcover P
  refine ⟨i, PrimeSpectrum.comap (ρ' i) q, ?_⟩
  apply PrimeSpectrum.ext
  change (q.asIdeal.comap (ρ' i)).comap (f i) = p.asIdeal
  rw [Ideal.comap_comap, hcomm i, ← Ideal.comap_comap]
  have hqI : q.asIdeal.comap (φ i) = P.asIdeal := congrArg PrimeSpectrum.asIdeal hq
  rw [hqI]
  exact hP

/-- The complementary principal-open chart supplies every point where
the selected hypersurface equation does not vanish. -/
theorem exists_localization_away_prime {R : Type u} [CommRing R]
    (z : R) (p : PrimeSpectrum R) (hz : z ∉ p.asIdeal) :
    ∃ q : PrimeSpectrum (Localization.Away z),
      PrimeSpectrum.comap (algebraMap R (Localization.Away z)) q = p := by
  have hdis : Disjoint (Submonoid.powers z : Set R) p.asIdeal :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime z).mpr hz
  have hQ := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers z)
    (Localization.Away z) p.asIdeal inferInstance hdis
  refine ⟨⟨p.asIdeal.map (algebraMap R (Localization.Away z)), hQ⟩, ?_⟩
  apply PrimeSpectrum.ext
  exact IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers z)
    (Localization.Away z) inferInstance hdis

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RefinementHelpers.Construction

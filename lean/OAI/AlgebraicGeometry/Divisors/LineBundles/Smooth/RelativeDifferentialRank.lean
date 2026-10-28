import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Relative Differential Rank -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.RelativeDifferentialRank.BundleCycles

noncomputable section

/-! The relative dimension of a locally standard smooth algebra is the
rank of its actual differential module at each prime, including on reducible bases. -/

theorem locallyStandardSmooth_differential_rank (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S]
    (n : ℕ) (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R S))
    (p : PrimeSpectrum S) : Module.rankAtStalk Ω[S⁄R] p = n := by
  classical
  obtain ⟨s, hs, hloc⟩ := h
  have hex : ∃ r ∈ s, r ∉ p.asIdeal := by
    by_contra hn
    have hle : Ideal.span s ≤ p.asIdeal := Ideal.span_le.mpr (by
      intro r hr
      by_contra hnr
      exact hn ⟨r, hr, hnr⟩)
    rw [hs] at hle
    exact p.isPrime.ne_top (top_le_iff.mp hle)
  obtain ⟨r, hr, hpr⟩ := hex
  let T := Localization.Away r
  have hst : Algebra.IsStandardSmoothOfRelativeDimension n R T := by
    have H := hloc r hr
    rw [← IsScalarTower.algebraMap_eq R S T,
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at H
    exact H
  let := hst
  have hmem : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S T)) := by
    rw [PrimeSpectrum.localization_away_comap_range T r]
    exact hpr
  obtain ⟨q, hq⟩ := hmem
  let : Nontrivial T := q.nontrivial
  let : Algebra.IsStandardSmooth R T := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers r)
  have H := Module.rankAtStalk_isBaseChange (KaehlerDifferential.isBaseChange_of_formallyEtale R S T) q
  rw [hq] at H
  have hn : Module.finrank T Ω[T⁄R] = n := Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := T) n)
  exact H.symm.trans ((congrFun (Module.rankAtStalk_eq_finrank_of_free (R := T) (M := Ω[T⁄R])) q).trans hn)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.RelativeDifferentialRank.BundleCycles

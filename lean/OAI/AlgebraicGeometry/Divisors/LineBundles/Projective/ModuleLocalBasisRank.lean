import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ModuleLocalBasis
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Module Local Basis Rank -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ModuleLocalBasisRank.BundleCycles

noncomputable section

/-! A principal local basis has the actual stalk rank at its chosen prime. -/

theorem projectiveModule_exists_localBasis_of_rank {R : Type} [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Projective R M] [Module.Finite R M]
    (p : PrimeSpectrum R) (n : ℕ) (hp : Module.rankAtStalk M p = n) :
    ∃ r : R, r ∉ p.asIdeal ∧ ∃ (ι : Type) (_ : Finite ι)
      (_ : Module.Basis ι (Localization.Away r) (LocalizedModule.Away r M)), Nat.card ι = n := by
  let : p.asIdeal.IsPrime := p.isPrime
  obtain ⟨r, hr, ι, hι, ⟨b⟩⟩ := ModuleLocalBasis.BundleCycles.projectiveModule_exists_localBasis M p.asIdeal
  let := hι
  let S := Localization.Away r
  let N := LocalizedModule.Away r M
  have hmem : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
    rw [PrimeSpectrum.localization_away_comap_range S r]
    exact hr
  obtain ⟨q, hq⟩ := hmem
  let : Nontrivial S := q.nontrivial
  let : Module.Free S N := Module.Free.of_basis b
  have H := Module.rankAtStalk_isBaseChange (LocalizedModule.isBaseChange (Submonoid.powers r) M) q
  rw [hq, hp] at H
  have hn : Module.finrank S N = Nat.card ι := Module.finrank_eq_nat_card_basis b
  have hqrank : Module.rankAtStalk N q = Nat.card ι :=
    (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := S) (M := N)) q).trans hn
  exact ⟨r, hr, ι, hι, b, hqrank.symm.trans H⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ModuleLocalBasisRank.BundleCycles

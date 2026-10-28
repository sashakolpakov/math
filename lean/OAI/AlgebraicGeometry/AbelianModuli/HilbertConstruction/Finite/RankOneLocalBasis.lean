import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FlatRankOneDescent

/-! # Rank One Local Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.RankOneLocalBasis

noncomputable section

/-! A finite flat module of constant rank one has an actual basis on a principal neighborhood of every prime. -/
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M]

theorem finiteFlatRankOne_localBasis
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = 1)
    (p : PrimeSpectrum R) :
    ∃ r ∉ p.asIdeal, Nonempty
      (LocalizedModule.Away r M ≃ₗ[Localization.Away r] Localization.Away r) := by
  obtain ⟨r, hr, hfree⟩ := Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant M p.asIdeal
    (fun m _ => (hrank ⟨m, inferInstance⟩).trans (hrank p).symm)
  let S := Localization.Away r
  let L := LocalizedModule.Away r M
  obtain ⟨q, hq⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
    rw [PrimeSpectrum.localization_away_comap_range S r]
    exact hr
  have : Nontrivial S := ⟨⟨0, 1, fun h => q.isPrime.one_notMem (h ▸ q.asIdeal.zero_mem)⟩⟩
  have heq : Module.finrank S L = 1 := by
    calc
      Module.finrank S L = Module.rankAtStalk L q :=
        (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := S) (M := L)) q).symm
      _ = Module.rankAtStalk M (q.comap (algebraMap R S)) :=
        Module.rankAtStalk_isBaseChange (LocalizedModule.isBaseChange (.powers r) M) q
      _ = 1 := hrank _
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one heq
  exact ⟨r, hr, ⟨e.symm⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.RankOneLocalBasis

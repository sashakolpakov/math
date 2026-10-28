import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.LocallyFree

/-! # Flat Rank One Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FlatRankOneDescent

noncomputable section

/-! A module whose faithfully flat scalar extension has an actual rank-one basis is finite, flat, has rank one at every prime, and is locally free. -/
open TensorProduct
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [AddCommGroup M] [Module R M]

theorem faithfullyFlat_rankOne_descent (e : S ⊗[R] M ≃ₗ[S] S) :
    Module.Finite R M ∧ Module.Flat R M ∧ ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = 1 := by
  have : Module.Finite S (S ⊗[R] M) := Module.Finite.equiv e.symm
  have : Module.Free S (S ⊗[R] M) := Module.Free.of_equiv e.symm
  have hf : Module.Finite R M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  have hflat : Module.Flat R M := Module.Flat.of_flat_tensorProduct R M S
  refine ⟨hf, hflat, ?_⟩
  intro p
  obtain ⟨q, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S) p
  have : Nontrivial S := ⟨⟨0, 1, fun h => q.isPrime.one_notMem (h ▸ q.asIdeal.zero_mem)⟩⟩
  calc
    Module.rankAtStalk M (q.comap (algebraMap R S)) = Module.rankAtStalk (S ⊗[R] M) q :=
      (Module.rankAtStalk_baseChange (R := R) (M := M) q).symm
    _ = Module.rankAtStalk (R := S) S q := congrFun (Module.rankAtStalk_eq_of_equiv e) q
    _ = 1 := congrFun (Module.rankAtStalk_self (R := S)) q

theorem faithfullyFlat_rankOne_locallyFree (e : S ⊗[R] M ≃ₗ[S] S)
    (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, Module.Free (Localization.Away r) (LocalizedModule.Away r M) := by
  obtain ⟨hf, hflat, hrank⟩ := faithfullyFlat_rankOne_descent e
  exact Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant M p
    (fun m _ => (hrank ⟨m, inferInstance⟩).trans (hrank ⟨p, inferInstance⟩).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FlatRankOneDescent

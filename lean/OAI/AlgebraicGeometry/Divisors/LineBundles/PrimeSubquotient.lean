import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-! # Prime Subquotient -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeSubquotient.BundleCycles

noncomputable section

/-!
# LineBundleCycles: prime cyclic subquotients of Noetherian modules

A nonzero module over a Noetherian ring contains an actual copy of R/p.
For a proper submodule N, its inverse image in M is a strictly larger
submodule whose quotient by N is this prime cyclic factor.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem exists_prime_cyclic_submodule [IsNoetherianRing R] [Nontrivial M] :
    ∃ (P : Submodule R M) (J : Ideal R), P ≠ ⊥ ∧ J.IsPrime ∧ Nonempty (P ≃ₗ[R] R ⧸ J) := by
  obtain ⟨J, hJ⟩ := associatedPrimes.nonempty R M
  obtain ⟨hp, u, hu⟩ := (isAssociatedPrime_iff_exists_injective_linearMap J M).mp hJ
  let : J.IsPrime := hp
  refine ⟨u.range, J, ?_, hp, ⟨(LinearEquiv.ofInjective u hu).symm⟩⟩
  intro hz
  have hm : u 1 ∈ u.range := ⟨1, rfl⟩
  rw [hz] at hm
  exact ((map_ne_zero_iff _ hu).mpr one_ne_zero) ((Submodule.mem_bot R).mp hm)

variable (N : Submodule R M) (P : Submodule R (M ⧸ N))

/-- Restrict the actual quotient map to the inverse image of a submodule. -/
def subquotientPreimageMap : P.comap N.mkQ →ₗ[R] P :=
  LinearMap.codRestrict P (N.mkQ.comp (P.comap N.mkQ).subtype) (fun x => x.2)

theorem subquotientPreimageMap_surjective : Function.Surjective (subquotientPreimageMap N P) := by
  intro x
  obtain ⟨m, hm⟩ := N.mkQ_surjective x.1
  refine ⟨⟨m, ?_⟩, Subtype.ext hm⟩
  exact (congrArg (fun q => q ∈ P) hm).mpr x.2

theorem subquotientPreimageMap_ker :
    (subquotientPreimageMap N P).ker = N.comap (P.comap N.mkQ).subtype := by
  ext x
  change (⟨N.mkQ x.1, x.2⟩ : P) = 0 ↔ x.1 ∈ N
  rw [Subtype.ext_iff]
  exact Submodule.Quotient.mk_eq_zero N

/-- The inverse-image quotient is canonically the original submodule of M/N. -/
def subquotientPreimageEquiv :
    ((P.comap N.mkQ) ⧸ N.comap (P.comap N.mkQ).subtype) ≃ₗ[R] P :=
  (Submodule.quotEquivOfEq _ _ (subquotientPreimageMap_ker N P).symm).trans
    ((subquotientPreimageMap N P).quotKerEquivOfSurjective (subquotientPreimageMap_surjective N P))

theorem subquotientPreimage_gt (hP : P ≠ ⊥) : N < P.comap N.mkQ := by
  have h := N.comapMkQOrderEmbedding.strictMono (bot_lt_iff_ne_bot.mpr hP)
  change (⊥ : Submodule R (M ⧸ N)).comap N.mkQ < P.comap N.mkQ at h
  rw [Submodule.comap_bot, Submodule.ker_mkQ] at h
  exact h

/-- Every proper submodule admits an actual strictly larger prime cyclic subquotient. -/
theorem exists_prime_cyclic_subquotient [IsNoetherianRing R] (hN : N ≠ ⊤) :
    ∃ (L : Submodule R M) (J : Ideal R), N < L ∧ J.IsPrime ∧
      Nonempty ((L ⧸ N.comap L.subtype) ≃ₗ[R] R ⧸ J) := by
  let : Nontrivial (M ⧸ N) := (Submodule.Quotient.nontrivial_iff).mpr hN
  obtain ⟨P, J, hP, hJ, ⟨e⟩⟩ := exists_prime_cyclic_submodule (R := R) (M := M ⧸ N)
  exact ⟨P.comap N.mkQ, J, subquotientPreimage_gt N P hP, hJ,
    ⟨(subquotientPreimageEquiv N P).trans e⟩⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeSubquotient.BundleCycles

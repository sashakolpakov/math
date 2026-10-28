import OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPadic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Place Exclusion -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceExclusion.CM

noncomputable section

/-! One positive rational integer excludes any finite set of number-field
places, uniformly for every embedding into a rational p-adic field. -/

open scoped Classical BigOperators
open _root_.NumberField IsDedekindDomain Filter

variable (F : Type) [Field F] [NumberField F]

def bound (S : Finset (HeightOneSpectrum (𝓞 F))) : ℕ := ∏ v ∈ S, v.asIdeal.absNorm

theorem bound_pos (S : Finset (HeightOneSpectrum (𝓞 F))) : 0 < bound F S := by
  apply Finset.prod_pos
  intro v _
  exact lt_trans Nat.zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)

theorem embedding_not_mem (S : Finset (HeightOneSpectrum (𝓞 F)))
    {q : ℕ} [Fact q.Prime] (hq : Nat.Coprime q (bound F S)) (f : F →+* ℚ_[q]) :
    PELModuli.CMPoints.LocalPadic.embeddingPlace f ∉ S := by
  intro hv
  have hm := (PELModuli.CMPoints.LocalPadic.embeddingPlace f).asIdeal.absNorm_mem
  change PELModuli.CMPoints.LocalPadic.embeddingResidue f
    ((PELModuli.CMPoints.LocalPadic.embeddingPlace f).asIdeal.absNorm : 𝓞 F) = 0 at hm
  rw [map_natCast] at hm
  have hd : q ∣ (PELModuli.CMPoints.LocalPadic.embeddingPlace f).asIdeal.absNorm :=
    (ZMod.natCast_eq_zero_iff _ _).mp hm
  have hb : q ∣ bound F S := hd.trans (Finset.dvd_prod_of_mem (fun v => v.asIdeal.absNorm) hv)
  have hq1 : q ∣ 1 := by simpa only [hq.gcd_eq_one] using Nat.dvd_gcd (dvd_refl q) hb
  exact (Fact.out : q.Prime).ne_one (Nat.dvd_one.mp hq1)

theorem exists_prime_bound (P : HeightOneSpectrum (𝓞 F) → Prop) (hP : ∀ᶠ v in Filter.cofinite, P v) :
    ∃ N : ℕ, 0 < N ∧ ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime q N →
      ∀ f : F →+* ℚ_[q], P (PELModuli.CMPoints.LocalPadic.embeddingPlace f) := by
  have hfinite : {v : HeightOneSpectrum (𝓞 F) | ¬ P v}.Finite := Filter.eventually_cofinite.mp hP
  let S := hfinite.toFinset
  refine ⟨bound F S, bound_pos F S, ?_⟩
  intro q _ hq f
  by_contra h
  have hm : PELModuli.CMPoints.LocalPadic.embeddingPlace f ∈ S := hfinite.mem_toFinset.mpr h
  exact embedding_not_mem F S hq f hm

theorem exists_embedding_bound {K : Type} [Field K] (j : F →+* K)
    (P : HeightOneSpectrum (𝓞 F) → Prop) (hP : ∀ᶠ v in Filter.cofinite, P v) :
    ∃ N : ℕ, 0 < N ∧ ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime q N →
      ∀ f : K →+* ℚ_[q], P (PELModuli.CMPoints.LocalPadic.embeddingPlace (f.comp j)) := by
  obtain ⟨N, hN, h⟩ := exists_prime_bound F P hP
  exact ⟨N, hN, fun q _ hq f => h q hq (f.comp j)⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceExclusion.CM

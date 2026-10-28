import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.PrimeLocalization

/-! # Unit Fractions -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.UnitFractions

noncomputable section

/-! Prime avoidance combines finitely many local unit fractions into
one numerator and denominator avoiding every selected prime. No normality
or dimension assumption on the domain is required. -/

open scoped Classical

universe u v w

variable (R : Type u) [CommRing R] [IsDomain R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
  {ι : Type w} [Fintype ι] [Nonempty ι] (P : ι → PrimeSpectrum R)

theorem exists_fraction (z : K)
    (hlocal : ∀ i, ∃ a b : R, a ∉ (P i).asIdeal ∧ b ∉ (P i).asIdeal ∧
      z = algebraMap R K a / algebraMap R K b) :
    ∃ a b : R, (∀ i, a ∉ (P i).asIdeal ∧ b ∉ (P i).asIdeal) ∧
      z = algebraMap R K a / algebraMap R K b := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R z
  have hb₀ : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbK : algebraMap R K b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb₀
  let I : Ideal R := (Ideal.span {b}).colon {a}
  have hD (i : ι) : ∃ d : R, d ∈ I ∧ d ∉ (P i).asIdeal := by
    obtain ⟨c, d, _, hd, he⟩ := hlocal i
    have hd₀ : d ≠ 0 := fun h => hd (h ▸ (P i).asIdeal.zero_mem)
    have hdK : algebraMap R K d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd₀
    have hcross : a * d = c * b := by
      apply IsFractionRing.injective R K
      simpa only [map_mul] using (div_eq_div_iff hbK hdK).mp (hab.trans he)
    refine ⟨d, ?_, hd⟩
    rw [Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton]
    exact ⟨c, by rw [mul_comm d a, hcross, mul_comm c b]⟩
  have hnot : ¬ (I : Set R) ⊆ ⋃ i ∈ (Finset.univ : Finset ι), ((P i).asIdeal : Set R) := by
    intro hs
    obtain ⟨i, _, hi⟩ := (Ideal.subset_union_prime (Classical.choice ‹Nonempty ι›)
      (Classical.choice ‹Nonempty ι›) (fun i _ _ _ => (P i).isPrime)).mp hs
    obtain ⟨d, hdI, hd⟩ := hD i
    exact hd (hi hdI)
  obtain ⟨d, hdI, hdout⟩ := Set.not_subset.mp hnot
  have hd (i : ι) : d ∉ (P i).asIdeal := fun h =>
    hdout (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ i, h⟩⟩)
  have hd₀ : d ≠ 0 := fun h => hd (Classical.choice ‹Nonempty ι›)
    (h ▸ (P _).asIdeal.zero_mem)
  have hdK : algebraMap R K d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd₀
  obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton.mp
    ((Submodule.mem_colon_singleton).mp hdI))
  have hfrac : z = algebraMap R K c / algebraMap R K d := by
    rw [← hab]
    apply (div_eq_div_iff hbK hdK).mpr
    change algebraMap R K a * algebraMap R K d = algebraMap R K c * algebraMap R K b
    rw [← map_mul, ← map_mul]
    apply congrArg (algebraMap R K)
    change d * a = b * c at hc
    calc
      a * d = d * a := mul_comm _ _
      _ = b * c := hc
      _ = c * b := mul_comm _ _
  refine ⟨c, d, fun i => ⟨?_, hd i⟩, hfrac⟩
  obtain ⟨u, v, hu, hv, he⟩ := hlocal i
  have hv₀ : v ≠ 0 := fun h => hv (h ▸ (P i).asIdeal.zero_mem)
  have hvK : algebraMap R K v ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hv₀
  have hcross : c * v = u * d := by
    apply IsFractionRing.injective R K
    simpa only [map_mul] using (div_eq_div_iff hdK hvK).mp (hfrac.symm.trans he)
  intro hcp
  have hm : u * d ∈ (P i).asIdeal := hcross ▸ (P i).asIdeal.mul_mem_right v hcp
  exact ((P i).isPrime.mem_or_mem hm).elim hu (hd i)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.UnitFractions

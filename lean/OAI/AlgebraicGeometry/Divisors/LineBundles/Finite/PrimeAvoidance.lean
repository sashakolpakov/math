import Mathlib.RingTheory.Ideal.Operations

/-! # Prime Avoidance -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PrimeAvoidance.BundleCycles

noncomputable section

/-! # LineBundleCycles: simultaneous avoidance of finitely many prime ideals and one arbitrary ideal -/

theorem finitePrimeAvoidance {R ι : Type*} [CommRing R] [Finite ι]
    (I J : Ideal R) (P : ι → Ideal R) (hP : ∀ i, (P i).IsPrime)
    (hJ : ¬ I ≤ J) (hI : ∀ i, ¬ I ≤ P i) :
    ∃ x : R, x ∈ I ∧ x ∉ J ∧ ∀ i, x ∉ P i := by
  classical
  let := Fintype.ofFinite ι
  let Q : Option ι → Ideal R := fun i => i.elim J P
  have hp : ∀ i ∈ (Finset.univ : Finset (Option ι)), i ≠ none → i ≠ none → (Q i).IsPrime := by
    intro i _ hi _
    cases i with
    | none => exact (hi rfl).elim
    | some i => exact hP i
  have hnot : ¬ (I : Set R) ⊆ ⋃ i ∈ (↑(Finset.univ : Finset (Option ι)) : Set (Option ι)), Q i := by
    intro h
    obtain ⟨i, _, hi⟩ := (Ideal.subset_union_prime none none hp).mp h
    cases i with
    | none => exact hJ hi
    | some i => exact hI i hi
  obtain ⟨x, hxI, hx⟩ := Set.not_subset.mp hnot
  refine ⟨x, hxI, ?_, ?_⟩
  · intro hxJ
    exact hx (Set.mem_iUnion.mpr ⟨none, Set.mem_iUnion.mpr ⟨Finset.mem_univ _, hxJ⟩⟩)
  · intro i hxi
    exact hx (Set.mem_iUnion.mpr ⟨some i, Set.mem_iUnion.mpr ⟨Finset.mem_univ _, hxi⟩⟩)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PrimeAvoidance.BundleCycles

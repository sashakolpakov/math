import Mathlib.RingTheory.Ideal.Operations

/-! # Prime Avoidance Coset -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PrimeAvoidanceCoset.Constructions

noncomputable section

/-! Prime avoidance inside a prescribed coset. For finitely many
incomparable prime ideals, an equation can be adjusted by an element
of the remaining-equation ideal without entering any of those primes. -/

universe u
variable {R : Type u} [CommRing R]

theorem exists_add_avoiding (s : Finset (Ideal R)) (hp : ∀ P ∈ s, P.IsPrime)
    (hs : ∀ P ∈ s, ∀ Q ∈ s, P ≤ Q → P = Q)
    (J : Ideal R) (x : R)
    (hI : ∀ P ∈ s, ¬ Ideal.span {x} ⊔ J ≤ P) :
    ∃ t ∈ J, ∀ P ∈ s, x + t ∉ P := by
  classical
  let good := s.filter (fun P => x ∉ P)
  let bad := s.filter (fun P => x ∈ P)
  let L := J ⊓ good.inf id
  have hL (P : Ideal R) (hP : P ∈ bad) : ¬ L ≤ P := by
    intro hLP
    have hPb := Finset.mem_filter.mp hP
    rcases (hp P hPb.1).inf_le.mp hLP with hJ | hgood
    · exact hI P hPb.1 (sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hPb.2)) hJ)
    · obtain ⟨Q, hQ, hQP⟩ := (hp P hPb.1).inf_le'.mp hgood
      have hQg := Finset.mem_filter.mp hQ
      have he := hs Q hQg.1 P hPb.1 hQP
      exact hQg.2 (he.symm ▸ hPb.2)
  have hnot : ¬ (L : Set R) ⊆ ⋃ P ∈ (bad : Set (Ideal R)), (P : Set R) := by
    intro h
    obtain ⟨P, hP, hLP⟩ :=
      (Ideal.subset_union_prime_finite bad.finite_toSet (f := id) ⊥ ⊥
        (fun P hP _ _ => hp P (Finset.mem_filter.mp hP).1)).mp h
    exact hL P hP hLP
  obtain ⟨t, ht, hnt⟩ := Set.not_subset.mp hnot
  refine ⟨t, ht.1, ?_⟩
  intro P hP hsum
  by_cases hx : x ∈ P
  · have hPb : P ∈ bad := Finset.mem_filter.mpr ⟨hP, hx⟩
    have htP : t ∈ P := by
      have h := P.sub_mem hsum hx
      rw [add_sub_cancel_left] at h
      exact h
    exact hnt (Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hPb, htP⟩⟩)
  · have hPg : P ∈ good := Finset.mem_filter.mpr ⟨hP, hx⟩
    have hle : good.inf id ≤ P := Finset.inf_le hPg
    have htP : t ∈ P := hle ht.2
    have h := P.sub_mem hsum htP
    rw [add_sub_cancel_right] at h
    exact hx h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PrimeAvoidanceCoset.Constructions

import OAI.AlgebraicGeometry.CycleClass.Thom.PrimeAvoidanceCoset
import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SequenceTailChange
import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.EquationQuotients

/-! # Regular Prime Equation -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Finite.RegularPrimeEquation.Constructions

noncomputable section

/-! A single elementary change of equations makes the head regular on
each member of a finite incomparable family of source primes. -/

open RingTheory.Sequence

open OAI.AlgebraicGeometry.CycleClass.Thom.PrimeAvoidanceCoset.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SequenceTailChange.Constructions

universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  (P : Finset (Ideal R)) (hp : ∀ Q ∈ P, Q.IsPrime)
  (ha : ∀ Q ∈ P, ∀ Q' ∈ P, Q ≤ Q' → Q = Q')
  (r : R) (rs : List R)
  (hr : IsWeaklyRegular R (r :: rs))
  (hm : ∀ x ∈ r :: rs, x ∈ IsLocalRing.maximalIdeal R)
  (hI : ∀ Q ∈ P, ¬ Ideal.ofList (r :: rs) ≤ Q)

include hp ha hr hm hI in
theorem exists_regular_head :
    ∃ t ∈ Ideal.ofList rs,
      Ideal.ofList ((r + t) :: rs) = Ideal.ofList (r :: rs) ∧
      IsWeaklyRegular R ((r + t) :: rs) ∧
      (∀ x ∈ (r + t) :: rs, x ∈ IsLocalRing.maximalIdeal R) ∧
      ∀ Q ∈ P, r + t ∉ Q ∧ IsSMulRegular (R ⧸ Q) (r + t) := by
  obtain ⟨t, ht, hn⟩ := PrimeAvoidanceCoset.Constructions.exists_add_avoiding P hp ha (Ideal.ofList rs) r (by
    simpa only [← Ideal.ofList_cons] using hI)
  refine ⟨t, ht, Regular.SequenceTailChange.Constructions.ofList_add_tail r t rs ht, Regular.SequenceTailChange.Constructions.weaklyRegular_add_tail R r t rs ht hm hr, ?_, ?_⟩
  · have htail : Ideal.ofList rs ≤ IsLocalRing.maximalIdeal R :=
      Ideal.span_le.mpr (fun x hx => hm x (List.mem_cons_of_mem r hx))
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · rw [hx]
      exact (IsLocalRing.maximalIdeal R).add_mem (hm r List.mem_cons_self) (htail ht)
    · exact hm x (List.mem_cons_of_mem r hx)
  · intro Q hQ
    refine ⟨hn Q hQ, (isSMulRegular_quotient_iff_mem_of_smul_mem Q (r + t)).mpr ?_⟩
    intro x hx
    exact ((hp Q hQ).mem_or_mem hx).resolve_left (hn Q hQ)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Finite.RegularPrimeEquation.Constructions

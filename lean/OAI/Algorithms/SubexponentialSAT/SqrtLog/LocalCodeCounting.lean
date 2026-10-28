import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-! Finite counting lemmas for the local-code exhaustive search. -/

namespace SubexponentialSAT.SqrtLog.LocalCode

open scoped BigOperators

theorem exists_avoiding_of_budget
    {A B : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (s : Finset B) (bad : B → Finset A) (K : ℕ)
    (hbudget : ∀ b ∈ s, (bad b).card * K ≤ Fintype.card A)
    (hsmall : s.card < K) :
    ∃ a : A, ∀ b ∈ s, a ∉ bad b := by
  classical
  by_contra h
  have hcover : Finset.univ ⊆ s.biUnion bad := by
    intro a _
    simp only [not_exists, not_forall, not_not] at h
    obtain ⟨b, hb, hab⟩ := h a
    exact Finset.mem_biUnion.mpr ⟨b, hb, hab⟩
  have hcard : Fintype.card A ≤ ∑ b ∈ s, (bad b).card := by
    exact (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
  have hmul : Fintype.card A * K ≤ s.card * Fintype.card A := by
    calc
      Fintype.card A * K ≤ (∑ b ∈ s, (bad b).card) * K :=
        Nat.mul_le_mul_right K hcard
      _ = ∑ b ∈ s, (bad b).card * K := Finset.sum_mul _ _ _
      _ ≤ ∑ _b ∈ s, Fintype.card A := Finset.sum_le_sum hbudget
      _ = s.card * Fintype.card A := by simp
  have hlt := Nat.mul_lt_mul_of_pos_right hsmall (Fintype.card_pos (α := A))
  rw [mul_comm] at hmul
  exact (not_lt_of_ge hmul) hlt

/-- Translation identifies an arbitrary fiber of a surjective homomorphism
with its zero fiber. This is the exact finite substitute for uniformity. -/
def fiberEquivZero {A B : Type*} [AddGroup A] [AddGroup B]
    (f : A →+ B) (b : B) (a : A) (ha : f a = b) :
    {x : A // f x = b} ≃ {x : A // f x = 0} where
  toFun x := ⟨x.1 - a, by rw [map_sub, x.2, ha, sub_self]⟩
  invFun x := ⟨x.1 + a, by rw [map_add, x.2, ha, zero_add]⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

theorem card_zero_fiber_mul
    {A B : Type*} [AddGroup A] [AddGroup B] [Fintype A] [Fintype B] [DecidableEq B]
    (f : A →+ B) (hf : Function.Surjective f) :
    Fintype.card {x : A // f x = 0} * Fintype.card B = Fintype.card A := by
  classical
  have hsame (b : B) :
      Fintype.card {x : A // f x = b} = Fintype.card {x : A // f x = 0} := by
    obtain ⟨a, ha⟩ := hf b
    exact Fintype.card_congr (fiberEquivZero f b a ha)
  have hsum := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  simpa only [Fintype.card_sigma, hsame, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_comm] using hsum

end SubexponentialSAT.SqrtLog.LocalCode

end OAI.Algorithms

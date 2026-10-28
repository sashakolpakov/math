import Mathlib.RingTheory.Filtration

/-! # Order -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Ideal.Order.Construction

noncomputable section

/-! Finite orders of nonzero ideals in Noetherian local rings, for Blowups. -/

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable (I J : Ideal R) (hI : I ≠ ⊤) (hJ : J ≠ ⊥)

include hI hJ in
/-- Krull intersection gives a finite, exact order for every nonzero ideal
with respect to a proper ideal of a Noetherian local ring. -/
theorem exists_idealAdicOrder : ∃ n : ℕ, J ≤ I ^ n ∧ ¬ J ≤ I ^ (n + 1) := by
  classical
  have hex : ∃ k : ℕ, ¬ J ≤ I ^ k := by
    by_contra h
    push Not at h
    apply hJ
    apply bot_unique
    rw [← I.iInf_pow_eq_bot_of_isLocalRing hI]
    exact le_iInf h
  have hk0 : Nat.find hex ≠ 0 := by
    intro hk
    have h := Nat.find_spec hex
    rw [hk, pow_zero, Ideal.one_eq_top] at h
    exact h le_top
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  refine ⟨n, ?_, ?_⟩
  · by_contra hbad
    have hle := Nat.find_min' hex hbad
    omega
  · simpa only [hn, Nat.succ_eq_add_one] using Nat.find_spec hex

/-- The finite order of an ideal, defined using the proved finite-order theorem. -/
def idealAdicOrder : ℕ := (exists_idealAdicOrder I J hI hJ).choose

theorem idealAdicOrder_spec :
    J ≤ I ^ idealAdicOrder I J hI hJ ∧ ¬ J ≤ I ^ (idealAdicOrder I J hI hJ + 1) :=
  (exists_idealAdicOrder I J hI hJ).choose_spec

/-- A power containment is exactly a lower bound on the ideal's order. -/
theorem le_idealAdicOrder_iff (n : ℕ) : n ≤ idealAdicOrder I J hI hJ ↔ J ≤ I ^ n := by
  constructor
  · intro hn
    exact (idealAdicOrder_spec I J hI hJ).1.trans (Ideal.pow_le_pow_right hn)
  · intro hpow
    by_contra hn
    have hsucc : idealAdicOrder I J hI hJ + 1 ≤ n := by omega
    exact (idealAdicOrder_spec I J hI hJ).2 (hpow.trans (Ideal.pow_le_pow_right hsucc))

/-- Exact power containment characterizes the order uniquely. -/
theorem idealAdicOrder_eq_iff (n : ℕ) :
    idealAdicOrder I J hI hJ = n ↔ J ≤ I ^ n ∧ ¬ J ≤ I ^ (n + 1) := by
  constructor
  · intro h
    simpa only [h] using idealAdicOrder_spec I J hI hJ
  · rintro ⟨hn, hn1⟩
    have hle := (le_idealAdicOrder_iff I J hI hJ n).mpr hn
    have hnle : ¬ n + 1 ≤ idealAdicOrder I J hI hJ := by
      intro h
      exact hn1 ((le_idealAdicOrder_iff I J hI hJ (n + 1)).mp h)
    omega

/-- Inclusion reverses the order of vanishing of nonzero ideals. -/
theorem idealAdicOrder_antitone {K : Ideal R} (hK : K ≠ ⊥) (hJK : J ≤ K) :
    idealAdicOrder I K hI hK ≤ idealAdicOrder I J hI hJ := by
  rw [le_idealAdicOrder_iff]
  exact hJK.trans (idealAdicOrder_spec I K hI hK).1

/-- The order of a sum of nonzero ideals is the minimum of their orders. -/
theorem idealAdicOrder_sup {K : Ideal R} (hK : K ≠ ⊥) (hsup : J ⊔ K ≠ ⊥) :
    idealAdicOrder I (J ⊔ K) hI hsup =
      min (idealAdicOrder I J hI hJ) (idealAdicOrder I K hI hK) := by
  apply le_antisymm
  · exact le_min
      (idealAdicOrder_antitone I J hI hJ hsup le_sup_left)
      (idealAdicOrder_antitone I K hI hK hsup le_sup_right)
  · rw [le_idealAdicOrder_iff]
    apply sup_le
    · exact (le_idealAdicOrder_iff I J hI hJ _).mp (min_le_left _ _)
    · exact (le_idealAdicOrder_iff I K hI hK _).mp (min_le_right _ _)

/-- Multiplication adds lower bounds on the orders of ideals. -/
theorem idealAdicOrder_mul_ge {K : Ideal R} (hK : K ≠ ⊥) (hmul : J * K ≠ ⊥) :
    idealAdicOrder I J hI hJ + idealAdicOrder I K hI hK ≤
      idealAdicOrder I (J * K) hI hmul := by
  rw [le_idealAdicOrder_iff, pow_add]
  exact Ideal.mul_mono (idealAdicOrder_spec I J hI hJ).1 (idealAdicOrder_spec I K hI hK).1

/-- Positive order is exactly containment in the center ideal. -/
theorem idealAdicOrder_pos_iff : 0 < idealAdicOrder I J hI hJ ↔ J ≤ I := by
  change 1 ≤ idealAdicOrder I J hI hJ ↔ J ≤ I
  simpa only [pow_one] using le_idealAdicOrder_iff I J hI hJ 1

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Ideal.Order.Construction

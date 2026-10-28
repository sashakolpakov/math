import Mathlib.RingTheory.AdicCompletion.Basic

/-! # Adic Sequence Differences -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.AdicSequenceDifferences

noncomputable section

/-! Successive differences in increasing ideal powers give the precise
congruences needed to lift compatible formal equations. -/

universe u
variable {R : Type u} [CommRing R]

theorem adic_sequence_difference (I : Ideal R) (n : ℕ) (z : ℕ → R)
    (h : ∀ k, z k - z (k + 1) ∈ I ^ (n + k)) :
    ∀ k l, k ≤ l → z k - z l ∈ I ^ (n + k) := by
  intro k l hkl
  induction l, hkl using Nat.le_induction with
  | base => simpa only [sub_self] using (I ^ (n + k)).zero_mem
  | succ l hkl ih =>
    have hs : z l - z (l + 1) ∈ I ^ (n + k) :=
      Ideal.pow_le_pow_right (Nat.add_le_add_left hkl n) (h l)
    convert (I ^ (n + k)).add_mem ih hs using 1
    abel

theorem adic_sequence_limit (I : Ideal R) [IsPrecomplete I R]
    (n : ℕ) (z : ℕ → R) (h : ∀ k, z k - z (k + 1) ∈ I ^ (n + k)) :
    ∃ a : R, (∀ k, z k - a ∈ I ^ k) ∧ z 0 - a ∈ I ^ n := by
  obtain ⟨a, ha⟩ := IsPrecomplete.prec (I := I) (M := R) inferInstance
    (f := z) (fun {k l} hkl => by
      apply SModEq.sub_mem.mpr
      simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using!
        (Ideal.pow_le_pow_right (Nat.le_add_left k n)
          (adic_sequence_difference I n z h k l hkl)))
  have ha' : ∀ k, z k - a ∈ I ^ k := by
    intro k
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using! (SModEq.sub_mem.mp (ha k))
  refine ⟨a, ha', ?_⟩
  have hz : z 0 - z n ∈ I ^ n := by
    simpa only [Nat.add_zero] using adic_sequence_difference I n z h 0 n (Nat.zero_le n)
  convert (I ^ n).add_mem hz (ha' n) using 1
  abel

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.AdicSequenceDifferences

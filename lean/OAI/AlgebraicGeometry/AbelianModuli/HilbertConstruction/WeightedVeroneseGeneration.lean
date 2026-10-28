import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.WeightedVeroneseExtraction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.MonomialAlgebra

/-! # Weighted Veronese Generation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.WeightedVeroneseGeneration

noncomputable section

/-! The explicit degree nL generates all monomials of degrees divisible
by nL. This proves generation in degree one after taking that Veronese algebra. -/
open scoped BigOperators Classical
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

theorem weightedExponentDegree_add {n : ℕ} (w a b : Fin n → ℕ) :
    WeightedVeroneseExtraction.weightedExponentDegree w (a + b) = WeightedVeroneseExtraction.weightedExponentDegree w a + WeightedVeroneseExtraction.weightedExponentDegree w b := by
  simp only [WeightedVeroneseExtraction.weightedExponentDegree, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem weightedExponentDegree_eq_zero_iff {n : ℕ} (w : Fin n → ℕ)
    (hw : ∀ i, 0 < w i) (a : Fin n → ℕ) : WeightedVeroneseExtraction.weightedExponentDegree w a = 0 ↔ a = 0 := by
  constructor
  · intro h
    funext i
    have hi := Finset.sum_eq_zero_iff.mp h i (Finset.mem_univ _)
    exact (Nat.mul_eq_zero.mp hi).resolve_right (Nat.ne_of_gt (hw i))
  · rintro rfl
    simp only [WeightedVeroneseExtraction.weightedExponentDegree, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

theorem weightedVeronese_monomial_mem_degree_adjoin {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (L : ℕ) (hL : 0 < L)
    (hwL : ∀ i, w i ∣ L) (D : Fin n → A) (a : Fin n → ℕ) (k : ℕ)
    (ha : WeightedVeroneseExtraction.weightedExponentDegree w a = k * (n * L)) :
    Balanced.MonomialAlgebra.exponentMonomial D a ∈ Algebra.adjoin R
      (Balanced.MonomialAlgebra.exponentMonomial D '' {b | WeightedVeroneseExtraction.weightedExponentDegree w b = n * L}) := by
  induction k generalizing a with
  | zero =>
    have hz : a = 0 := (weightedExponentDegree_eq_zero_iff w hw a).mp (by simpa using ha)
    rw [hz, Balanced.MonomialAlgebra.exponentMonomial_zero]
    exact (Algebra.adjoin R _).one_mem
  | succ k ih =>
    obtain ⟨b, hb, hbdeg⟩ := WeightedVeroneseExtraction.weightedVeronese_exists_subexponent hn w hw L hL hwL a
      (k + 1) (Nat.succ_pos _) ha
    have hab : a - b + b = a := by
      funext i
      exact Nat.sub_add_cancel (hb i)
    have hrem : WeightedVeroneseExtraction.weightedExponentDegree w (a - b) = k * (n * L) := by
      have hsum := weightedExponentDegree_add w (a - b) b
      rw [hab, ha, hbdeg, Nat.succ_mul] at hsum
      exact Nat.add_right_cancel hsum.symm
    have h₁ := ih (a - b) hrem
    have h₂ : Balanced.MonomialAlgebra.exponentMonomial D b ∈ Algebra.adjoin R
        (Balanced.MonomialAlgebra.exponentMonomial D '' {b | WeightedVeroneseExtraction.weightedExponentDegree w b = n * L}) :=
      Algebra.subset_adjoin ⟨b, hbdeg, rfl⟩
    have hp := (Algebra.adjoin R _).mul_mem h₁ h₂
    rw [← Balanced.MonomialAlgebra.exponentMonomial_add, hab] at hp
    exact hp

theorem weightedVeronese_adjoin_eq_degree_adjoin {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (L : ℕ) (hL : 0 < L)
    (hwL : ∀ i, w i ∣ L) (D : Fin n → A) :
    Algebra.adjoin R (Balanced.MonomialAlgebra.exponentMonomial D '' {a | n * L ∣ WeightedVeroneseExtraction.weightedExponentDegree w a}) =
      Algebra.adjoin R (Balanced.MonomialAlgebra.exponentMonomial D '' {a | WeightedVeroneseExtraction.weightedExponentDegree w a = n * L}) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨a, ⟨k, hk⟩, rfl⟩
    apply weightedVeronese_monomial_mem_degree_adjoin hn w hw L hL hwL D a k
    exact hk.trans (Nat.mul_comm _ _)
  · apply Algebra.adjoin_mono
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha.symm ▸ dvd_refl _, rfl⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.WeightedVeroneseGeneration

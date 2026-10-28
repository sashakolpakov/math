import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteOrderLinearCongruence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoprimeIntegerModuleDivision

/-! # Coprime Finite Order Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoprimeFiniteOrderCongruence

noncomputable section

/-! In an additively torsion-free ring, a finite-order element whose order is coprime to the modulus satisfies arbitrarily deep powers of its original congruence. -/

universe u

variable {R : Type u} [Ring R] [IsAddTorsionFree R]

theorem coprime_finiteOrder_congruence_square (u : R) (m n : ℕ) (hm : m ≠ 0)
    (hcop : n.Coprime m) (hu : u ^ n = 1) (x : R) (hx : m • x = u - 1) :
    ∃ y : R, (m ^ 2) • y = u - 1 := by
  have he : u = 1 + m • x := by rw [hx]; abel
  obtain ⟨c, hc⟩ := FiniteOrderLinearCongruence.ringFiniteOrder_linearCoefficient_divisible x m n hm
    ((congrArg (fun a : R => a ^ n) he).symm.trans hu)
  obtain ⟨y, hy⟩ := CoprimeIntegerModuleDivision.coprime_nsmul_division n m hcop x c hc
  refine ⟨y, ?_⟩
  rw [pow_two, mul_smul, hy]
  exact hx

theorem coprime_finiteOrder_congruence_doublePowers (u : R) (m n : ℕ) (hm : m ≠ 0)
    (hcop : n.Coprime m) (hu : u ^ n = 1) (h : ∃ x : R, m • x = u - 1) (k : ℕ) :
    ∃ y : R, (m ^ (2 ^ k)) • y = u - 1 := by
  induction k with
  | zero => simpa only [pow_zero, pow_one] using h
  | succ k ih =>
    obtain ⟨x, hx⟩ := ih
    obtain ⟨y, hy⟩ := coprime_finiteOrder_congruence_square u (m ^ (2 ^ k)) n
      (pow_ne_zero _ hm) (hcop.pow_right _) hu x hx
    have he : (m ^ (2 ^ k)) ^ 2 = m ^ (2 ^ (k + 1)) := by rw [← pow_mul, pow_succ]
    exact ⟨y, (congrArg (fun a : ℕ => a • y) he).symm.trans hy⟩

theorem coprime_finiteOrder_congruence_allPowers (u : R) (m n : ℕ) (hm : m ≠ 0)
    (hcop : n.Coprime m) (hu : u ^ n = 1) (h : ∃ x : R, m • x = u - 1) (k : ℕ) :
    ∃ y : R, (m ^ k) • y = u - 1 := by
  obtain ⟨y, hy⟩ := coprime_finiteOrder_congruence_doublePowers u m n hm hcop hu h k
  have hk : k ≤ 2 ^ k := (Nat.lt_two_pow_self (n := k)).le
  have he : k + (2 ^ k - k) = 2 ^ k := by omega
  refine ⟨(m ^ (2 ^ k - k)) • y, ?_⟩
  rw [← mul_smul, ← pow_add, he]
  exact hy

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoprimeFiniteOrderCongruence

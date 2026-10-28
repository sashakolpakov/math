import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-! # Total Product Signs -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TotalProductSigns

/-! The Koszul sign identity for totalizing a product of cochain
complexes. It is valid in every additive abelian group. -/

variable {V : Type*} [AddCommGroup V]

theorem product_rule (p a q n : ℕ) (hn : p + a = n) (A B C D : V) :
    (-1 : ℤ) ^ (a * q) •
        ((A + (-1 : ℤ) ^ p • B) + (-1 : ℤ) ^ (p + q) • (C + (-1 : ℤ) ^ a • D)) =
      ((-1 : ℤ) ^ (a * q) • A + (-1 : ℤ) ^ p • ((-1 : ℤ) ^ ((a + 1) * q) • C)) +
        (-1 : ℤ) ^ n •
          ((-1 : ℤ) ^ (a * (q + 1)) • B + (-1 : ℤ) ^ q • ((-1 : ℤ) ^ (a * q) • D)) := by
  have hc : p + (a + 1) * q = a * q + (p + q) := by
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have hd : n + (q + a * q) = a * q + (p + q + a) := by omega
  have hb : (-1 : ℤ) ^ (n + a * (q + 1)) = (-1 : ℤ) ^ (a * q + p) := by
    rw [neg_one_pow_eq_pow_mod_two (n + a * (q + 1)), neg_one_pow_eq_pow_mod_two (a * q + p)]
    congr 1
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  simp only [smul_add, smul_smul, ← pow_add, hc, hd, hb]
  abel

end OAI.NumberTheory.PadicHodge.IntegralComparison.TotalProductSigns

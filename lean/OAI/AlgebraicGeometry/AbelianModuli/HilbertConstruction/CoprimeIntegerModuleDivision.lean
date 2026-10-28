import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Module.NatInt

/-! # Coprime Integer Module Division -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoprimeIntegerModuleDivision

noncomputable section

/-! Bezout's identity removes a coprime integer factor from divisibility in any abelian group. -/

universe u

variable {M : Type u} [AddCommGroup M]

theorem coprime_nsmul_division (n m : ℕ) (hcop : n.Coprime m) (x c : M)
    (hc : n • x = m • c) : ∃ y : M, m • y = x := by
  let a := Nat.gcdA n m
  let b := Nat.gcdB n m
  have hab : (n : ℤ) * a + (m : ℤ) * b = 1 := by
    simpa only [hcop.gcd_eq_one, Int.natCast_one] using (Nat.gcd_eq_gcd_ab n m).symm
  refine ⟨a • c + b • x, ?_⟩
  calc
    m • (a • c + b • x) = a • (m • c) + b • (m • x) := by
      rw [nsmul_add, smul_comm m a c, smul_comm m b x]
    _ = a • (n • x) + b • (m • x) := congrArg (fun z => a • z + b • (m • x)) hc.symm
    _ = ((n : ℤ) * a + (m : ℤ) * b) • x := by
      simp only [add_smul, mul_smul, natCast_zsmul]
      rw [smul_comm a n x, smul_comm b m x]
    _ = x := by rw [hab, one_smul]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoprimeIntegerModuleDivision

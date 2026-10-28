import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeKernels

/-! # Coprime Power Roots -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CoprimePowerRoots.Construction

/-! A bounded-exponent group has canonical Bezout roots for every
coprime exponent. These formulas apply to full scheme-valued point groups. -/

universe u
variable {G : Type u} [CommGroup G]

theorem coprimePowerRoot_pow (n d : ℕ) (hnd : n.Coprime d) (x : G) (hx : x ^ d = 1) :
    (x ^ n.gcdA d) ^ n = x := by
  have hb := Picard.PoincareBundle.CoprimeKernels.bezout n d hnd
  calc
    (x ^ n.gcdA d) ^ n = x ^ ((n : ℤ) * n.gcdA d) := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm]
    _ = x ^ ((n : ℤ) * n.gcdA d) * (x ^ d) ^ n.gcdB d := by rw [hx, one_zpow, mul_one]
    _ = x ^ ((n : ℤ) * n.gcdA d + (d : ℤ) * n.gcdB d) := by
      rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    _ = x := by rw [hb, zpow_one]

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CoprimePowerRoots.Construction

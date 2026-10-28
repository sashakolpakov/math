import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! # Cubical Algebra Pow -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubicalAlgebraPow.Construction.CubicalAlgebra

/-! The algebraic consequence of a symmetric cubical identity.
This file does not assert the geometric theorem of the cube. -/

universe u v

section Additive

variable {G : Type u} {P : Type v} [AddCommGroup G] [AddCommGroup P]
variable (q : G → P) (hzero : q 0 = 0) (heven : ∀ x, q (-x) = q x)
variable (hcube : ∀ x y z, q (x + y + z) + q x + q y + q z =
  q (x + y) + q (x + z) + q (y + z))

include hzero heven hcube

theorem parallelogram (x y : G) :
    q (x + y) + q (x - y) = 2 • q x + 2 • q y := by
  have h := hcube x y (-y)
  rw [add_neg_cancel_right, add_neg_cancel, hzero, heven] at h
  rw [← sub_eq_add_neg, add_zero] at h
  simpa only [two_nsmul, add_assoc] using h.symm

/-- A symmetric function satisfying the cubical identity is quadratic on
every cyclic subgroup, without any torsion-free hypothesis on the target. -/
theorem nsmul (a : G) (n : ℕ) : q (n • a) = (n * n) • q a := by
  induction n using Nat.twoStepInduction with
  | zero => simpa only [zero_nsmul, Nat.zero_mul] using hzero
  | one => simp only [one_nsmul, Nat.one_mul]
  | more n hn hn₁ =>
    have h := parallelogram q hzero heven hcube ((n + 1) • a) a
    have hp : (n + 1) • a + a = (n + 2) • a := by
      simp only [add_nsmul, one_nsmul, two_nsmul, add_assoc]
    have hm : (n + 1) • a - a = n • a := by
      rw [add_nsmul, one_nsmul, add_sub_cancel_right]
    rw [hp, hm, hn, hn₁] at h
    apply add_right_cancel (b := (n * n) • q a)
    calc
      q ((n + 2) • a) + (n * n) • q a =
          2 • ((n + 1) * (n + 1)) • q a + 2 • q a := h
      _ = ((n + 2) * (n + 2)) • q a + (n * n) • q a := by
        rw [← mul_nsmul, ← add_nsmul, ← add_nsmul]
        congr 1
        ring

end Additive

variable {A : Type u} {B : Type v} [CommGroup A] [CommGroup B]

/-- Multiplicative form, for use with tensor products in a Picard group. -/
theorem pow (q : A → B) (hone : q 1 = 1) (hinv : ∀ a, q a⁻¹ = q a)
    (hcube : ∀ a b c, q (a * b * c) * q a * q b * q c =
      q (a * b) * q (a * c) * q (b * c)) (a : A) (n : ℕ) :
    q (a ^ n) = q a ^ (n * n) := by
  exact @nsmul (Additive A) (Additive B) _ _
    (fun x => Additive.ofMul (q x.toMul)) hone hinv hcube (Additive.ofMul a) n

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubicalAlgebraPow.Construction.CubicalAlgebra

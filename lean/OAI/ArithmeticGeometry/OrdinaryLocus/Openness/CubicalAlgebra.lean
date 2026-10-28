import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardField
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! # Cubical Algebra -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CubicalAlgebra.Construction

/-! The algebraic consequence of the theorem-of-the-cube identity. -/

universe u v

def IsCubical {G : Type u} {H : Type v} [AddCommGroup G] [AddCommGroup H]
    (q : G → H) : Prop :=
  ∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)

theorem cubical_double_of_symmetric {G : Type u} {H : Type v}
    [AddCommGroup G] [AddCommGroup H] {q : G → H}
    (h0 : q 0 = 0) (hc : IsCubical q) (x : G) (hx : q (-x) = q x) :
    q (x + x) = 4 • q x := by
  have h := hc x x (-x)
  simp only [add_neg_cancel_right, add_neg_cancel, h0, hx, add_zero] at h
  calc
    q (x + x) = q x + q x + q x + q x := h.symm
    _ = 4 • q x := by abel

theorem cubical_nsmul_of_symmetric {G : Type u} {H : Type v}
    [AddCommGroup G] [AddCommGroup H] {q : G → H}
    (h0 : q 0 = 0) (hc : IsCubical q) (x : G) (hx : q (-x) = q x) (n : ℕ) :
    q (n • x) = n ^ 2 • q x := by
  have htwo := cubical_double_of_symmetric h0 hc x hx
  induction n using Nat.twoStepInduction with
  | zero => simpa using h0
  | one => simp
  | more n hn hn1 =>
    have h := hc (n • x) x x
    have h₁ : n • x + x = (n + 1) • x := by simp [add_nsmul]
    have h₂ : n • x + x + x = (n + 2) • x := by simp [add_nsmul, two_nsmul, add_assoc]
    rw [h₂, h₁, hn, hn1, htwo] at h
    apply add_right_cancel (b := n ^ 2 • q x + q x + q x)
    calc
      q ((n + 2) • x) + (n ^ 2 • q x + q x + q x) =
          (n + 1) ^ 2 • q x + (n + 1) ^ 2 • q x + 4 • q x := by simpa [add_assoc] using h
      _ = (n + 2) ^ 2 • q x + (n ^ 2 • q x + q x + q x) := by
        have hp : (n + 1) ^ 2 + (n + 1) ^ 2 + 4 = (n + 2) ^ 2 + (n ^ 2 + 1 + 1) := by ring
        simpa only [add_nsmul, one_nsmul] using congrArg (fun m : ℕ ↦ m • q x) hp

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CubicalAlgebra.Construction

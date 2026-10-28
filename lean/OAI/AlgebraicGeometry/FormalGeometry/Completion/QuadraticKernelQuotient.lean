import OAI.AlgebraicGeometry.FormalGeometry.Completion.NonnegativeQuadraticMk
import OAI.AlgebraicGeometry.FormalGeometry.Completion.QuadraticHeightDescent

/-! # Quadratic Kernel Quotient -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! A fixed integral normalization of a nonnegative quadratic function
gives a discrete positive height on the quotient by its actual zero subgroup. -/

universe u

variable {G : Type u} [AddCommGroup G] (q : NonnegativeQuadraticMk.Construction.NonnegativeQuadratic G)

theorem NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.quotientValue_nonneg (x : G ⧸ q.zeroKernel) : 0 ≤ q.quotientValue x := by
  induction x using Quotient.inductionOn' with
  | h x => exact q.nonneg x

theorem NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.quotientValue_eq_zero_iff (x : G ⧸ q.zeroKernel) : q.quotientValue x = 0 ↔ x = 0 := by
  induction x using Quotient.inductionOn' with
  | h x => exact (QuotientAddGroup.eq_zero_iff (N := q.zeroKernel) x).symm

def NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.quotientQuadratic : NonnegativeQuadraticMk.Construction.NonnegativeQuadratic (G ⧸ q.zeroKernel) where
  value := q.quotientValue
  zero := q.zero
  nonneg := q.quotientValue_nonneg
  parallelogram x y := by
    induction x using Quotient.inductionOn' with
    | h x =>
      induction y using Quotient.inductionOn' with
      | h y => exact q.parallelogram x y

def NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.quotientHeight (D : ℕ) (hD : 0 < D)
    (hint : ∀ x : G, ∃ z : ℤ, (D : ℚ) * q.value x = z) :
    QuadraticHeightDescent.Construction.DiscreteQuadraticHeight (G ⧸ q.zeroKernel) where
  value x := (D : ℝ) * (q.quotientValue x : ℝ)
  zero := by change (D : ℝ) * (q.value 0 : ℝ) = 0; rw [q.zero, Rat.cast_zero, mul_zero]
  positive x hx := by
    induction x using Quotient.inductionOn' with
    | h x =>
      have hq : q.value x ≠ 0 := by
        intro h
        exact hx ((q.quotientValue_eq_zero_iff (QuotientAddGroup.mk x)).mp h)
      have hp := mul_pos (Nat.cast_pos.mpr hD : (0 : ℚ) < D) (lt_of_le_of_ne (q.nonneg x) hq.symm)
      obtain ⟨z, hz⟩ := hint x
      rw [hz] at hp
      have hzpos : 0 < z := by exact_mod_cast hp
      have hzR : (D : ℝ) * (q.value x : ℝ) = (z : ℝ) := by exact_mod_cast hz
      change 1 ≤ (D : ℝ) * (q.value x : ℝ)
      rw [hzR]
      exact_mod_cast (show (1 : ℤ) ≤ z by omega)
  parallelogram x y := by
    have h := congrArg (fun a : ℚ => (a : ℝ)) (q.quotientQuadratic.parallelogram x y)
    push_cast at h
    change (D : ℝ) * (q.quotientValue (x + y) : ℝ) + (D : ℝ) * (q.quotientValue (x - y) : ℝ) = _
    change (q.quotientValue (x + y) : ℝ) + (q.quotientValue (x - y) : ℝ) =
      2 * ((q.quotientValue x : ℝ) + (q.quotientValue y : ℝ)) at h
    nlinarith

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion

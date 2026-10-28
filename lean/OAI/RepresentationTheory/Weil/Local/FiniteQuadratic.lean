import OAI.RepresentationTheory.Weil.Local.Gaussian
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.NumberTheory.GaussSum

/-! # Finite Quadratic -/

namespace OAI.RepresentationTheory.Weil.Local.FiniteQuadratic.Construction

noncomputable section

/-! Quadratic characters on finite additive groups, for the local Gaussian phase. -/

open scoped Classical ComplexConjugate

structure QuadraticCharacter (A : Type*) [AddCommGroup A] where
  toFun : A → ℂ
  polar : AddChar A (AddChar A ℂ)
  map_zero : toFun 0 = 1
  map_neg : ∀ x, toFun (-x) = toFun x
  map_add : ∀ x y, toFun (x + y) = toFun x * toFun y * polar x y
  norm_eq_one : ∀ x, ‖toFun x‖ = 1

namespace QuadraticCharacter

variable {A : Type*} [AddCommGroup A]

instance : CoeFun (QuadraticCharacter A) (fun _ => A → ℂ) := ⟨toFun⟩

theorem ne_zero (q : QuadraticCharacter A) (x : A) : q x ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [q.norm_eq_one]
  exact one_ne_zero

theorem polar_symmetric (q : QuadraticCharacter A) (x y : A) : q.polar x y = q.polar y x := by
  apply mul_left_cancel₀ (mul_ne_zero (q.ne_zero x) (q.ne_zero y))
  rw [← q.map_add, mul_comm (q x) (q y), ← q.map_add, add_comm]

theorem polar_self (q : QuadraticCharacter A) (x : A) : q.polar x x = q x ^ 2 := by
  have h := q.map_add x (-x)
  rw [add_neg_cancel, q.map_zero, q.map_neg, (q.polar x).map_neg_eq_inv] at h
  have hne : q.polar x x ≠ 0 := ((q.polar x).val_isUnit x).ne_zero
  have h' := congrArg (fun z : ℂ => z * q.polar x x) h
  simpa only [one_mul, mul_assoc, inv_mul_cancel₀ hne, mul_one, pow_two] using h'

theorem map_nsmul (q : QuadraticCharacter A) (n : ℕ) (x : A) :
    q (n • x) = q x ^ (n ^ 2) := by
  induction n with
  | zero => simp [q.map_zero]
  | succ n ih =>
    rw [add_nsmul, one_nsmul, q.map_add, ih, q.polar.map_nsmul_eq_pow]
    simp only [AddChar.pow_apply, q.polar_self]
    rw [← pow_mul, ← pow_succ, ← pow_add]
    congr 1
    ring

def Nondegenerate (q : QuadraticCharacter A) : Prop := ∀ x, q.polar x = 1 → x = 0

def gauss [Fintype A] (q : QuadraticCharacter A) : ℂ := ∑ x, q x

theorem mul_conj_self (q : QuadraticCharacter A) (x : A) : q x * conj (q x) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, q.norm_eq_one]
  norm_num

theorem gauss_mul_conj [Fintype A] (q : QuadraticCharacter A) (hq : q.Nondegenerate) :
    q.gauss * conj q.gauss = (Fintype.card A : ℂ) := by
  have hshift (y : A) : (∑ x, q (x + y)) = ∑ x, q x :=
    Equiv.sum_comp (Equiv.addRight y) q
  have hsum (x : A) : (∑ y, q.polar x y) = if x = 0 then (Fintype.card A : ℂ) else 0 := by
    by_cases hx : x = 0
    · subst x
      simp [q.polar.map_zero_eq_one]
    · have hp : q.polar x ≠ 1 := fun h => hx (hq x h)
      simp only [ite_eq_right hx]
      exact AddChar.sum_eq_zero_of_ne_one hp
  calc
    _ = ∑ y, (∑ x, q (x + y)) * conj (q y) := by
      simp only [hshift, ← Finset.mul_sum, ← map_sum, QuadraticCharacter.gauss]
    _ = ∑ x, q x * ∑ y, q.polar x y := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [q.map_add]
      calc
        _ = (q x * q.polar x y) * (q y * conj (q y)) := by ring
        _ = _ := by rw [q.mul_conj_self, mul_one]
    _ = _ := by simp [hsum, q.map_zero]

theorem gauss_norm_sq [Fintype A] (q : QuadraticCharacter A) (hq : q.Nondegenerate) :
    ‖q.gauss‖ ^ 2 = (Fintype.card A : ℝ) := by
  have h := q.gauss_mul_conj hq
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

theorem gauss_ne_zero [Fintype A] (q : QuadraticCharacter A) (hq : q.Nondegenerate) :
    q.gauss ≠ 0 := by
  intro h
  have hs := q.gauss_norm_sq hq
  rw [h, norm_zero, zero_pow (by decide)] at hs
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hs.symm

end QuadraticCharacter

end

end OAI.RepresentationTheory.Weil.Local.FiniteQuadratic.Construction

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTernary
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore

namespace OAI.Algorithms

/-! Concrete coefficient choices over `ZMod (3^t)` and specialization to
the actual unramified counting ring. -/

namespace SubexponentialSAT.SqrtLog.Idempotent

open Polynomial
attribute [local instance] Classical.propDecidable

def half (t : ℕ) : ZMod (3 ^ t) := (((3 ^ t + 1) / 2 : ℕ) : ZMod (3 ^ t))

theorem twice_half (t : ℕ) : (2 : ZMod (3 ^ t)) * half t = 1 := by
  have hm : 3 ^ t % 2 = 1 := by simp [Nat.pow_mod]
  have hn : 2 * ((3 ^ t + 1) / 2) = 3 ^ t + 1 := by omega
  unfold half
  calc
    (2 : ZMod (3 ^ t)) * (((3 ^ t + 1) / 2 : ℕ) : ZMod (3 ^ t)) =
        ((2 * ((3 ^ t + 1) / 2) : ℕ) : ZMod (3 ^ t)) := by push_cast; rfl
    _ = ((3 ^ t + 1 : ℕ) : ZMod (3 ^ t)) := congrArg (fun n : ℕ => (n : ZMod (3 ^ t))) hn
    _ = 1 := by rw [Nat.cast_add, ZMod.natCast_self, Nat.cast_one, zero_add]

theorem modulus_gt_one {t : ℕ} (ht : 0 < t) : 1 < 3 ^ t := by
  cases t with
  | zero => omega
  | succ n =>
      rw [pow_succ]
      have : 0 < 3 ^ n := Nat.pow_pos (by decide)
      omega

noncomputable def baseCoefficients (t : ℕ) : Fin t → (ZMod (3 ^ t))[X] :=
  coefficients (half t) t

theorem baseCoefficients_degree {t : ℕ} (ht : 0 < t) (s : Fin t) :
    (baseCoefficients t s).natDegree < 3 := by
  let : Fact (1 < 3 ^ t) := ⟨modulus_gt_one ht⟩
  exact coefficients_degree (half t) t s

theorem prime_three_cases (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem primeField_residue_cases (d : ℕ) (y : RingCore.E d)
    (hy : ∃ a : ZMod 3, y = algebraMap (ZMod 3) (RingCore.E d) a) :
    y = 0 ∨ y = 1 ∨ y = 2 := by
  obtain ⟨a, rfl⟩ := hy
  rcases prime_three_cases a with h | h | h
  · left; simp only [h, map_zero]
  · right; left; simp only [h, map_one]
  · right; right; rw [h, map_two]

theorem actual_H_nilpotent (d t : ℕ) (ht : 0 < t) (x : RingCore.O d t)
    (hx : ∃ a : ZMod 3, RingCore.rho d t ht x =
      algebraMap (ZMod 3) (RingCore.E d) a) :
    ((ternaryH : (ZMod (3 ^ t))[X]).eval₂ (RingCore.base d t) x) ^ t = 0 :=
  eval_H_nilpotent (RingCore.base d t) (RingCore.rho d t ht) 3 t
    (fun y hy => (RingCore.rho_eq_zero_iff d t ht y).mp hy)
    (RingCore.prime_power_zero d t) x (primeField_residue_cases d _ hx)

theorem actual_coefficients_indicator (d t : ℕ) (ht : 0 < t) (x : RingCore.O d t)
    (hx : ∃ a : ZMod 3, RingCore.rho d t ht x =
      algebraMap (ZMod 3) (RingCore.E d) a) :
    (∑ s : Fin t, (baseCoefficients t s).eval₂ (RingCore.base d t) x *
      ((ternaryH : (ZMod (3 ^ t))[X]).eval₂ (RingCore.base d t) x) ^ (s : ℕ)) =
      if RingCore.rho d t ht x = 0 then 1 else 0 := by
  classical
  exact coefficients_indicator (RingCore.base d t) (RingCore.rho d t ht)
    (half t) (twice_half t) 3 t
    (fun y hy => (RingCore.rho_eq_zero_iff d t ht y).mp hy)
    (RingCore.prime_power_zero d t) x (primeField_residue_cases d _ hx)

end SubexponentialSAT.SqrtLog.Idempotent

end OAI.Algorithms

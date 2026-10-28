import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentBase
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel

namespace OAI.Algorithms

/-! The idempotent specification specialized to the execution-supplied
irreducible polynomial, rather than the semantic minimum-polynomial model. -/
namespace SubexponentialSAT.SqrtLog.Idempotent

open Polynomial
attribute [local instance] Classical.propDecidable

theorem model_residue_cases {d : ℕ} (a : RingModel.Data d) (y : a.E)
    (hy : ∃ c : ZMod 3, y = algebraMap (ZMod 3) a.E c) :
    y = 0 ∨ y = 1 ∨ y = 2 := by
  obtain ⟨c, rfl⟩ := hy
  rcases prime_three_cases c with h | h | h
  · left; simp only [h, map_zero]
  · right; left; simp only [h, map_one]
  · right; right; rw [h, map_two]

theorem model_H_nilpotent {d : ℕ} (a : RingModel.Data d) (t : ℕ)
    (ht : 0 < t) (x : a.O t)
    (hx : ∃ c : ZMod 3, a.rho t ht x = algebraMap (ZMod 3) a.E c) :
    ((ternaryH : (ZMod (3 ^ t))[X]).eval₂ (a.base t) x) ^ t = 0 :=
  eval_H_nilpotent (a.base t) (a.rho t ht) 3 t
    (fun y hy => (a.rho_eq_zero_iff t ht y).mp hy)
    (a.prime_power_zero t) x (model_residue_cases a _ hx)

theorem model_coefficients_indicator {d : ℕ} (a : RingModel.Data d)
    (t : ℕ) (ht : 0 < t) (x : a.O t)
    (hx : ∃ c : ZMod 3, a.rho t ht x = algebraMap (ZMod 3) a.E c) :
    (∑ s : Fin t, (baseCoefficients t s).eval₂ (a.base t) x *
      ((ternaryH : (ZMod (3 ^ t))[X]).eval₂ (a.base t) x) ^ (s : ℕ)) =
      if a.rho t ht x = 0 then 1 else 0 := by
  exact coefficients_indicator (a.base t) (a.rho t ht)
    (half t) (twice_half t) 3 t
    (fun y hy => (a.rho_eq_zero_iff t ht y).mp hy)
    (a.prime_power_zero t) x (model_residue_cases a _ hx)

end SubexponentialSAT.SqrtLog.Idempotent

end OAI.Algorithms

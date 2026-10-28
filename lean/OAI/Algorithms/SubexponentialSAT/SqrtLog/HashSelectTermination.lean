import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectGreedy

namespace OAI.Algorithms

/-! Entirely integer termination for the finite greedy selector. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

theorem two_step_halving {a b c : ℕ}
    (h₁ : 3 * b ≤ 2 * a) (h₂ : 3 * c ≤ 2 * b) : 2 * c ≤ a := by
  omega

theorem geometric_bound (f : ℕ → ℕ) (s : ℕ)
    (h : ∀ i < 2 * s, 3 * f (i + 1) ≤ 2 * f i) :
    2 ^ s * f (2 * s) ≤ f 0 := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hi := ih (fun i hi => h i (by omega))
    have htwo : 2 * f (2 * s + 2) ≤ f (2 * s) :=
      two_step_halving (h (2 * s) (by omega)) (h (2 * s + 1) (by omega))
    calc
      2 ^ (s + 1) * f (2 * (s + 1)) = 2 ^ s * (2 * f (2 * s + 2)) := by
        rw [pow_succ]
        have ht : 2 * (s + 1) = 2 * s + 2 := by omega
        rw [ht]
        ring
      _ ≤ 2 ^ s * f (2 * s) := Nat.mul_le_mul_left _ htwo
      _ ≤ f 0 := hi

theorem zero_of_contraction (f : ℕ → ℕ) (s : ℕ)
    (h : ∀ i < 2 * s, 3 * f (i + 1) ≤ 2 * f i)
    (hstart : f 0 < 2 ^ s) : f (2 * s) = 0 := by
  have hg := (geometric_bound f s h).trans_lt hstart
  have hp : 0 < 2 ^ s := by positivity
  by_contra hn
  have hone : 1 ≤ f (2 * s) := Nat.one_le_iff_ne_zero.mpr hn
  have hlo := Nat.mul_le_mul_left (2 ^ s) hone
  simp only [Nat.mul_one] at hlo
  omega

/-- `Nat.size` is binary length, so this cap uses no real logarithm. -/
def loopCap (n m : ℕ) : ℕ := 2 * (n + Nat.size m + 1)

theorem initial_mass_lt_cap_power {X R : Type*} [Fintype X]
    (rowAccept : R → X → Bool) (weight : X → ℕ) (initial : List R)
    (n m : ℕ) (hx : Fintype.card X ≤ 2 ^ n) (hw : ∀ x, weight x ≤ m) :
    mass rowAccept weight initial < 2 ^ (n + Nat.size m + 1) := by
  have hm := Nat.lt_size_self m
  calc
    mass rowAccept weight initial ≤ Fintype.card X * m :=
      mass_le rowAccept weight initial m hw
    _ ≤ 2 ^ n * m := Nat.mul_le_mul_right m hx
    _ < 2 ^ n * 2 ^ Nat.size m := Nat.mul_lt_mul_of_pos_left hm (by positivity)
    _ ≤ 2 ^ (n + Nat.size m + 1) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)

theorem run_zero_at_cap {X R : Type*} [Fintype X] {c : ℕ}
    (rowAccept : R → X → Bool) (weight : X → ℕ)
    (evaluate : List R → ℕ) (family : Fin (c + 1) → R) (initial : List R)
    (n m : ℕ) (hx : Fintype.card X ≤ 2 ^ n) (hw : ∀ x, weight x ≤ m)
    (hsound : ∀ t < loopCap n m, ∀ i,
      evaluate (family i :: run evaluate family initial t) =
        mass rowAccept weight (family i :: run evaluate family initial t))
    (hcoverage : ∀ t < loopCap n m, ∀ x,
      accepts rowAccept (run evaluate family initial t) x = true → 0 < weight x →
      3 * survivingCandidates rowAccept family x ≤ 2 * (c + 1)) :
    mass rowAccept weight (run evaluate family initial (loopCap n m)) = 0 := by
  apply zero_of_contraction (fun t => mass rowAccept weight (run evaluate family initial t))
    (n + Nat.size m + 1)
  · intro i hi
    exact next_contraction rowAccept weight evaluate family _
      (hsound i hi) (hcoverage i hi)
  · exact initial_mass_lt_cap_power rowAccept weight initial n m hx hw

theorem run_zero_from_initial_coverage {X R : Type*} [Fintype X] {c : ℕ}
    (rowAccept : R → X → Bool) (weight : X → ℕ)
    (evaluate : List R → ℕ) (family : Fin (c + 1) → R) (initial : List R)
    (n m : ℕ) (hx : Fintype.card X ≤ 2 ^ n) (hw : ∀ x, weight x ≤ m)
    (hsound : ∀ t < loopCap n m, ∀ i,
      evaluate (family i :: run evaluate family initial t) =
        mass rowAccept weight (family i :: run evaluate family initial t))
    (hcoverage : ∀ x, accepts rowAccept initial x = true → 0 < weight x →
      3 * survivingCandidates rowAccept family x ≤ 2 * (c + 1)) :
    mass rowAccept weight (run evaluate family initial (loopCap n m)) = 0 := by
  apply run_zero_at_cap rowAccept weight evaluate family initial n m hx hw hsound
  intro t _ x hx hw
  exact hcoverage x (run_accepts_initial rowAccept evaluate family initial t x hx) hw

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms

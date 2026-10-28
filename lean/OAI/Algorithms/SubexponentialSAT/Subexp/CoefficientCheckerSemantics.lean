import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientDynamics

namespace OAI.Algorithms

/-! Value semantics of the physical parity/head checker. These definitions
specify the outputs of the fixed control program; no execution is assigned to
these pure functions. -/

namespace SubexponentialSAT.Subexp.CoefficientCheckerSemantics

variable {K : Type*} [CommRing K]

def sign (negative : Bool) : K := if negative then -1 else 1

def advanceParity : ℕ → Bool → Bool
  | 0, b => b
  | n + 1, b => advanceParity n (!b)

@[simp] theorem sign_false : (sign false : K) = 1 := rfl
@[simp] theorem sign_true : (sign true : K) = -1 := rfl

theorem sign_not (b : Bool) : (sign (!b) : K) = -sign b := by
  cases b <;> simp [sign]

theorem sign_advanceParity (n : ℕ) (b : Bool) :
    (sign (advanceParity n b) : K) = (-1 : K)^n * sign b := by
  induction n generalizing b with
  | zero => simp [advanceParity]
  | succ n ih =>
    rw [advanceParity, ih, sign_not, pow_succ]
    ring

theorem advanceParity_add (m n : ℕ) (b : Bool) :
    advanceParity (m + n) b = advanceParity n (advanceParity m b) := by
  induction m generalizing b with
  | zero => simp [advanceParity]
  | succ m ih =>
    simpa only [Nat.succ_add, advanceParity] using ih (!b)

variable [DecidableEq K]

/-- The finite conjunction implemented by R successive physical head tests. -/
def checkHeads : ℕ → Bool → List K → Bool
  | 0, _, _ => true
  | n + 1, b, xs =>
    decide (xs.getD 0 0 = sign b) && checkHeads n (!b) (CoefficientDynamics.shift xs)

/-- The recursion tests precisely the successive shifted heads. -/
theorem checkHeads_true_iff (n : ℕ) (b : Bool) (xs : List K) :
    checkHeads n b xs = true ↔
      ∀ d < n, (CoefficientDynamics.shifts d xs).getD 0 0 = sign (advanceParity d b) := by
  induction n generalizing b xs with
  | zero => simp [checkHeads]
  | succ n ih =>
    rw [checkHeads, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hhead, hrest⟩ d hd
      cases d with
      | zero => simpa [CoefficientDynamics.shifts, advanceParity] using hhead
      | succ d =>
        have h := (ih (!b) (CoefficientDynamics.shift xs)).mp hrest d
          (Nat.lt_of_succ_lt_succ hd)
        simpa only [CoefficientDynamics.shifts, advanceParity] using h
    · intro h
      refine ⟨?_, (ih (!b) (CoefficientDynamics.shift xs)).mpr ?_⟩
      · simpa [CoefficientDynamics.shifts, advanceParity] using h 0 (Nat.zero_lt_succ n)
      · intro d hd
        have hs := h (d + 1) (Nat.succ_lt_succ hd)
        simpa only [CoefficientDynamics.shifts, advanceParity] using hs

/-- The actual shifted-head tests are exactly the normalized binomial
interpolation equations for the interval starting at A. -/
theorem checkHeads_normalized (A R : ℕ) (xs : List K) :
    checkHeads R (advanceParity A false) (CoefficientDynamics.shifts A xs) = true ↔
      ∀ d < R, CoefficientDynamics.evaluate xs (A + d) = (-1 : K)^(A + d) := by
  rw [checkHeads_true_iff]
  apply forall_congr'
  intro d
  apply forall_congr'
  intro _
  rw [CoefficientDynamics.head_shifts, CoefficientDynamics.evaluate_shifts,
    sign_advanceParity, sign_advanceParity, sign_false, mul_one, pow_add]
  rw [mul_comm ((-1 : K)^d)]

/-- The outer search is guaranteed to encounter a satisfying coefficient
vector; this theorem supplies existence only, not the search implementation. -/
theorem exists_checkHeads {K : Type*} [Field K] [DecidableEq K] (h2 : (2 : K) ≠ 0) (A R : ℕ) :
    ∃ xs : List K, xs.length = R ∧
      checkHeads R (advanceParity A false) (CoefficientDynamics.shifts A xs) = true := by
  obtain ⟨xs, hlen, hxs⟩ := CoefficientDynamics.exists_normalized h2 A R
  refine ⟨xs, hlen, (checkHeads_normalized A R xs).mpr ?_⟩
  intro d hd
  exact hxs ⟨d, hd⟩

end SubexponentialSAT.Subexp.CoefficientCheckerSemantics

end OAI.Algorithms

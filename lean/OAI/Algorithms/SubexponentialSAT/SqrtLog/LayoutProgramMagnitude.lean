import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithmMagnitude

namespace OAI.Algorithms

/-! Unsigned component-total budgets for the signed-pair implementation.
These bounds do not infer component size from the absolute signed difference.
The physical arithmetic refinement must prove its total obeys this recurrence. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open scoped BigOperators

/-- The nonnegative recurrence for one scalar numerator. Sign swaps leave this
quantity unchanged, and pair addition/multiplication have no cancellation. -/
def scalarMass (R d h : ℕ) (coefficientMass : ℕ → ℕ) : ℕ :=
  ∑ k ∈ Finset.range (R-d),
    coefficientMass (d+k) * 2^(R-1-(d+k)) * h.choose k

theorem scalarMass_le_raw (R d h Q : ℕ) (hQ : 1 ≤ Q) (hh : h ≤ Q)
    (coefficientMass : ℕ → ℕ)
    (hc : ∀ j < R, coefficientMass j ≤ (4*Q)^R) :
    scalarMass R d h coefficientMass ≤ R * (4*Q)^R * 2^R * Q^R := by
  calc
    _ ≤ ∑ _k ∈ Finset.range (R-d), (4*Q)^R * 2^R * Q^R := by
      apply Finset.sum_le_sum
      intro k hk
      have hkR : k < R-d := Finset.mem_range.mp hk
      have hj : d+k < R := by omega
      have hchoose : h.choose k ≤ Q^R :=
        ((Nat.choose_le_pow h k).trans (Nat.pow_le_pow_left hh k)).trans
          (Nat.pow_le_pow_right hQ (by omega))
      exact Nat.mul_le_mul
        (Nat.mul_le_mul (hc _ hj) (Nat.pow_le_pow_right (by omega) (by omega))) hchoose
    _ ≤ R * (4*Q)^R * 2^R * Q^R := by
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
      calc
        _ ≤ R * ((4*Q)^R * 2^R * Q^R) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        _ = _ := by ring

theorem scalarMass_le (R d h Q : ℕ) (hQ : 1 ≤ Q) (hh : h ≤ Q)
    (coefficientMass : ℕ → ℕ)
    (hc : ∀ j < R, coefficientMass j ≤ (4*Q)^R) :
    scalarMass R d h coefficientMass ≤ (8*Q)^(2*R) := by
  have hR : R ≤ 2^R := Nat.le_of_lt Nat.lt_two_pow_self
  calc
    _ ≤ R * (4*Q)^R * 2^R * Q^R := scalarMass_le_raw R d h Q hQ hh _ hc
    _ ≤ 2^R * (4*Q)^R * 2^R * Q^R := by gcongr
    _ = (16*Q^2)^R := by simp only [← mul_pow]; congr 1; ring
    _ ≤ (64*Q^2)^R := by gcongr; norm_num
    _ = (8*Q)^(2*R) := by rw [pow_mul]; congr 1; ring

/-- A consumer needs a bound on each component, not just on their difference. -/
theorem scalar_components_le (R d h Q positive negative : ℕ)
    (hQ : 1 ≤ Q) (hh : h ≤ Q) (coefficientMass : ℕ → ℕ)
    (hc : ∀ j < R, coefficientMass j ≤ (4*Q)^R)
    (htotal : positive + negative ≤ scalarMass R d h coefficientMass) :
    positive ≤ (8*Q)^(2*R) ∧ negative ≤ (8*Q)^(2*R) := by
  have htotal' := htotal.trans (scalarMass_le R d h Q hQ hh coefficientMass hc)
  omega

/-- Safe full cleared-constraint budget, including the diagonal denominator. -/
def constraintMassBound (Q R : ℕ) : ℕ := (8*Q)^(2*R) + 2^(R-1)

theorem constraint_components_le (Q R positive negative numeratorMass : ℕ)
    (hnum : numeratorMass ≤ (8*Q)^(2*R))
    (htotal : positive + negative ≤ numeratorMass + 2^(R-1)) :
    positive ≤ constraintMassBound Q R ∧ negative ≤ constraintMassBound Q R := by
  unfold constraintMassBound
  omega

/-- Summing an incidence fiber grows unsigned total at most linearly in the
number of copies. Repetitions are counted; no cancellation is used. -/
theorem fiberMass_le {I : Type*} (fiber : List I) (mass : I → ℕ) (B : ℕ)
    (h : ∀ i ∈ fiber, mass i ≤ B) :
    (fiber.map mass).sum ≤ fiber.length * B := by
  induction fiber with
  | nil => simp
  | cons i fiber ih =>
      have hi := h i (by simp)
      have ht := ih (fun j hj => h j (by simp [hj]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

theorem pullback_components_le {I : Type*} (fiber : List I)
    (positive negative : I → ℕ) (Q R P N : ℕ)
    (h : ∀ i ∈ fiber, positive i + negative i ≤ constraintMassBound Q R)
    (hP : P = (fiber.map positive).sum) (hN : N = (fiber.map negative).sum) :
    P + N ≤ fiber.length * constraintMassBound Q R ∧
      N ≤ fiber.length * constraintMassBound Q R := by
  have hs : (fiber.map (fun i => positive i + negative i)).sum = P + N := by
    rw [hP,hN]
    induction fiber with
    | nil => simp
    | cons i fiber ih => simp []; omega
  have hbound := fiberMass_le fiber (fun i => positive i + negative i)
    (constraintMassBound Q R) h
  rw [hs] at hbound
  exact ⟨hbound, by omega⟩

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-! Exact natural-valued mass for finite sparse-hash selection.
The row semantics are abstract here; no evaluator is assumed computable
from this definition at the target cost. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

open scoped BigOperators

variable {X R I : Type*}

def accepts (rowAccept : R → X → Bool) (rows : List R) (x : X) : Bool :=
  rows.all (fun r => rowAccept r x)

@[simp] theorem accepts_nil (rowAccept : R → X → Bool) (x : X) :
    accepts rowAccept [] x = true := rfl

@[simp] theorem accepts_cons (rowAccept : R → X → Bool) (r : R)
    (rows : List R) (x : X) :
    accepts rowAccept (r :: rows) x = (rowAccept r x && accepts rowAccept rows x) := rfl

def mass [Fintype X] (rowAccept : R → X → Bool) (weight : X → ℕ)
    (rows : List R) : ℕ :=
  ∑ x, if accepts rowAccept rows x then weight x else 0

theorem mass_eq_zero_iff [Fintype X] (rowAccept : R → X → Bool)
    (weight : X → ℕ) (rows : List R) :
    mass rowAccept weight rows = 0 ↔
      ∀ x, accepts rowAccept rows x = true → weight x = 0 := by
  simp only [mass, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_const]
  constructor
  · intro h x hx
    simpa [hx] using h x
  · intro h x
    cases hx : accepts rowAccept rows x <;> simp [hx, h x]

theorem mass_le [Fintype X] (rowAccept : R → X → Bool)
    (weight : X → ℕ) (rows : List R) (m : ℕ)
    (hw : ∀ x, weight x ≤ m) :
    mass rowAccept weight rows ≤ Fintype.card X * m := by
  calc
    mass rowAccept weight rows ≤ ∑ _x : X, m := by
      apply Finset.sum_le_sum
      intro x _
      cases hx : accepts rowAccept rows x <;> simp [ hw x]
    _ = Fintype.card X * m := by simp

theorem mass_cons_le [Fintype X] (rowAccept : R → X → Bool)
    (weight : X → ℕ) (rows : List R) (r : R) :
    mass rowAccept weight (r :: rows) ≤ mass rowAccept weight rows := by
  apply Finset.sum_le_sum
  intro x _
  cases h : rowAccept r x <;> cases ha : accepts rowAccept rows x <;>
    simp [accepts_cons, h, ha]

theorem accepts_of_forall (rowAccept : R → X → Bool) (rows : List R)
    (x : X) (h : ∀ r ∈ rows, rowAccept r x = true) :
    accepts rowAccept rows x = true := by
  exact List.all_eq_true.mpr h

theorem mass_zero_accepts_iff [Fintype X] (rowAccept : R → X → Bool)
    (weight : X → ℕ) (rows : List R)
    (hz : mass rowAccept weight rows = 0)
    (hs : ∀ x, weight x = 0 → ∀ r ∈ rows, rowAccept r x = true) :
    ∀ x, accepts rowAccept rows x = true ↔ weight x = 0 := by
  intro x
  constructor
  · exact (mass_eq_zero_iff rowAccept weight rows).mp hz x
  · intro hx
    exact accepts_of_forall rowAccept rows x (hs x hx)

def survivingCandidates [Fintype I] (rowAccept : R → X → Bool)
    (family : I → R) (x : X) : ℕ :=
  ∑ i, if rowAccept (family i) x then 1 else 0

theorem survival_bound_of_detection [Fintype I]
    (rowAccept : R → X → Bool) (family : I → R) (x : X)
    (hdetect : Fintype.card I ≤
      3 * (Finset.univ.filter (fun i => rowAccept (family i) x = false)).card) :
    3 * survivingCandidates rowAccept family x ≤ 2 * Fintype.card I := by
  classical
  have hsurv : survivingCandidates rowAccept family x =
      (Finset.univ.filter (fun i => rowAccept (family i) x = true)).card := by
    simp [survivingCandidates]
  have hp := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset I)) (fun i => rowAccept (family i) x = true)
  have hf : (Finset.univ.filter (fun i => ¬ rowAccept (family i) x = true)) =
      Finset.univ.filter (fun i => rowAccept (family i) x = false) := by
    ext i
    cases h : rowAccept (family i) x <;> simp [h]
  rw [hf] at hp
  simp only [Finset.card_univ] at hp
  omega

theorem sum_trial_mass [Fintype X] [Fintype I]
    (rowAccept : R → X → Bool) (weight : X → ℕ)
    (family : I → R) (rows : List R) :
    (∑ i, mass rowAccept weight (family i :: rows)) =
      ∑ x, if accepts rowAccept rows x then
        survivingCandidates rowAccept family x * weight x else 0 := by
  simp only [mass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases ha : accepts rowAccept rows x
  · simp [ha, accepts_cons]
  · simp only [accepts_cons, ha, Bool.and_true, ↓reduceIte]
    rw [survivingCandidates, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    cases hr : rowAccept (family i) x <;> simp []

theorem average_trial_contraction [Fintype X] [Fintype I]
    (rowAccept : R → X → Bool) (weight : X → ℕ)
    (family : I → R) (rows : List R)
    (hcoverage : ∀ x, accepts rowAccept rows x = true → 0 < weight x →
      3 * survivingCandidates rowAccept family x ≤ 2 * Fintype.card I) :
    3 * (∑ i, mass rowAccept weight (family i :: rows)) ≤
      2 * Fintype.card I * mass rowAccept weight rows := by
  rw [sum_trial_mass, mass, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  cases ha : accepts rowAccept rows x
  · simp []
  · simp only [ ↓reduceIte]
    by_cases hw : weight x = 0
    · simp [hw]
    · have h := Nat.mul_le_mul_right (weight x)
        (hcoverage x ha (Nat.pos_of_ne_zero hw))
      simpa [Nat.mul_assoc] using h

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms

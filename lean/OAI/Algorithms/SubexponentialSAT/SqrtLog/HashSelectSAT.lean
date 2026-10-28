import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectTermination
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectQueries
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInput

namespace OAI.Algorithms

/-! Instantiation of the finite selector with actual clause violations.
This is a conditional composition theorem: exact evaluation and initial
coverage are explicit hypotheses, not an assumed SAT oracle. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

open scoped BigOperators

abbrev Row (m : ℕ) := Fin m → ZMod 3

def cnfRowAccept {n m : ℕ} (C : Fin m → SAT.Clause (Fin n))
    (r : Row m) (x : SAT.Assignment (Fin n)) : Bool :=
  decide ((∑ e, r e * HashInput.violationVector (R := ZMod 3) C x e) = 0)

theorem cnfRowAccept_of_zero {n m : ℕ} (C : Fin m → SAT.Clause (Fin n))
    (x : SAT.Assignment (Fin n)) (hx : HashInput.violationWeight C x = 0)
    (r : Row m) : cnfRowAccept C r x = true := by
  have hs := (HashInput.violationWeight_eq_zero_iff C x).mp hx
  have hv := HashInput.violationVector_of_satisfied (R := ZMod 3) C x hs
  simp [cnfRowAccept, hv]

theorem cnf_mass_zero_iff {n m : ℕ} (C : Fin m → SAT.Clause (Fin n))
    (rows : List (Row m)) (hzero : mass (cnfRowAccept C) (HashInput.violationWeight C) rows = 0) :
    ∀ x, accepts (cnfRowAccept C) rows x = true ↔ ∀ e, (C e).eval x = true := by
  intro x
  rw [← HashInput.violationWeight_eq_zero_iff C x]
  apply mass_zero_accepts_iff (cnfRowAccept C) (HashInput.violationWeight C) rows hzero
  intro y hy r _
  exact cnfRowAccept_of_zero C y hy r

def acceptedCount {X R : Type*} [Fintype X] (rowAccept : R → X → Bool)
    (rows : List R) : ℕ := ∑ x, if accepts rowAccept rows x then 1 else 0

theorem acceptedCount_pos_iff {X R : Type*} [Fintype X]
    (rowAccept : R → X → Bool) (rows : List R) :
    0 < acceptedCount rowAccept rows ↔ ∃ x, accepts rowAccept rows x = true := by
  classical
  simp [acceptedCount]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa using hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa using hx⟩

theorem cnf_decision_of_zero {n m : ℕ} (C : Fin m → SAT.Clause (Fin n))
    (rows : List (Row m))
    (hzero : mass (cnfRowAccept C) (HashInput.violationWeight C) rows = 0) :
    0 < acceptedCount (cnfRowAccept C) rows ↔ ∃ x, ∀ e, (C e).eval x = true := by
  rw [acceptedCount_pos_iff]
  exact exists_congr (cnf_mass_zero_iff C rows hzero)

theorem select_cnf_correct {n m c : ℕ} (C : Fin m → SAT.Clause (Fin n))
    (evaluate : List (Row m) → ℕ) (family : Fin (c + 1) → Row m)
    (initial : List (Row m))
    (hsound : ∀ t < loopCap n m, ∀ i,
      evaluate (family i :: run evaluate family initial t) =
        mass (cnfRowAccept C) (HashInput.violationWeight C)
          (family i :: run evaluate family initial t))
    (hcoverage : ∀ x, accepts (cnfRowAccept C) initial x = true →
      0 < HashInput.violationWeight C x →
      3 * survivingCandidates (cnfRowAccept C) family x ≤ 2 * (c + 1)) :
    ∀ x, accepts (cnfRowAccept C) (run evaluate family initial (loopCap n m)) x = true ↔
      ∀ e, (C e).eval x = true := by
  apply cnf_mass_zero_iff
  apply run_zero_from_initial_coverage (cnfRowAccept C) (HashInput.violationWeight C)
    evaluate family initial n m
  · simp [SAT.Assignment]
  · intro x
    simpa using HashInput.violationWeight_le C x
  · exact hsound
  · exact hcoverage

theorem list_scope_cost_le {n m : ℕ} (C : Fin m → SAT.Clause (Fin n))
    (rows : List (Row m)) (k : ℕ) (hwidth : ∀ e, (C e).card ≤ k) :
    totalCost (fun r => (HashInput.hashScope C r).card) rows ≤
      k * totalCost (fun r => (HashInput.rowSupport r).card) rows := by
  induction rows with
  | nil => simp [totalCost]
  | cons r rows ih =>
    simp only [totalCost_cons]
    calc
      _ ≤ k * (HashInput.rowSupport r).card +
          k * totalCost (fun r => (HashInput.rowSupport r).card) rows :=
        Nat.add_le_add (HashInput.card_hashScope_le C r k hwidth) ih
      _ = _ := by ring

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms

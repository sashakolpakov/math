import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectSAT
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamilyEnumeration
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeBasic

namespace OAI.Algorithms

/-! The concrete indexed tuple family discharges the selector's coverage
hypothesis from a supplied lower-support code. All tuples, including repeated
coordinates and repeated resulting rows, remain in the enumeration. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

open scoped BigOperators

def tupleRows (m d : ℕ) : Fin ((3 * m) ^ d) → Row m :=
  fun i => HashFamily.row (HashFamily.enumerate m d i)

def tupleFamily {m d c : ℕ} (hcount : (3 * m) ^ d = c + 1) :
    Fin (c + 1) → Row m :=
  fun i => tupleRows m d (Fin.cast hcount.symm i)

theorem rowSupport_card_eq_supportCard {m : ℕ} (r : Row m) :
    (HashInput.rowSupport r).card = HashFamily.supportCard r := by
  unfold HashFamily.supportCard
  congr 1
  ext e
  simp [HashInput.rowSupport]

theorem tupleFamily_support {m d c : ℕ} (hcount : (3 * m) ^ d = c + 1)
    (i : Fin (c + 1)) :
    (HashInput.rowSupport (tupleFamily hcount i)).card ≤ d := by
  rw [rowSupport_card_eq_supportCard]
  exact HashFamily.enumerate_row_support_le m d (Fin.cast hcount.symm i)

theorem tupleRows_survival {n m d : ℕ} (C : Fin m → SAT.Clause (Fin n))
    (x : SAT.Assignment (Fin n)) (hm : 0 < m)
    (heavy : m ≤ d * HashFamily.supportCard
      (HashInput.violationVector (R := ZMod 3) C x)) :
    3 * survivingCandidates (cnfRowAccept C) (tupleRows m d) x ≤
      2 * (3 * m) ^ d := by
  have hd := HashFamily.enumerate_detection
    (HashInput.violationVector (R := ZMod 3) C x) hm heavy
  have h : 3 * survivingCandidates (cnfRowAccept C) (tupleRows m d) x ≤
      2 * Fintype.card (Fin ((3 * m) ^ d)) := by
    apply survival_bound_of_detection (cnfRowAccept C) (tupleRows m d) x
    have hcard :
        ({i | cnfRowAccept C (tupleRows m d i) x = false} :
          Finset (Fin ((3 * m) ^ d))).card =
        ({i | ∑ e, HashFamily.row (HashFamily.enumerate m d i) e *
          HashInput.violationVector (R := ZMod 3) C x e ≠ 0} :
          Finset (Fin ((3 * m) ^ d))).card := by
      apply Finset.card_bij' (fun i _ => i) (fun i _ => i)
      · intro i hi
        have hbool := (Finset.mem_filter.mp hi).2
        have hne : ∑ e, HashFamily.row (HashFamily.enumerate m d i) e *
            HashInput.violationVector (R := ZMod 3) C x e ≠ 0 :=
          decide_eq_false_iff_not.mp hbool
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
      · intro i hi
        have hne := (Finset.mem_filter.mp hi).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact decide_eq_false_iff_not.mpr hne
      · intro i hi
        rfl
      · intro i hi
        rfl
    simpa only [Fintype.card_fin, hcard] using hd
  simpa using h

theorem tupleFamily_survival {n m d c : ℕ} (C : Fin m → SAT.Clause (Fin n))
    (hcount : (3 * m) ^ d = c + 1) (x : SAT.Assignment (Fin n)) (hm : 0 < m)
    (heavy : m ≤ d * HashFamily.supportCard
      (HashInput.violationVector (R := ZMod 3) C x)) :
    3 * survivingCandidates (cnfRowAccept C) (tupleFamily hcount) x ≤
      2 * (c + 1) := by
  have hs : survivingCandidates (cnfRowAccept C) (tupleFamily hcount) x =
      survivingCandidates (cnfRowAccept C) (tupleRows m d) x := by
    exact Fintype.sum_equiv (finCongr hcount.symm) _ _ (fun _ => rfl)
  rw [hs, ← hcount]
  exact tupleRows_survival C x hm heavy

theorem supportCard_eq_codeWeight {m : ℕ} (v : Fin m → ZMod 3) :
    HashFamily.supportCard v = SparseCode.weight v := rfl

theorem rowSupport_card_eq_codeWeight {m : ℕ} (r : Row m) :
    (HashInput.rowSupport r).card = SparseCode.weight r :=
  (rowSupport_card_eq_supportCard r).trans (supportCard_eq_codeWeight r)

theorem initial_coverage_of_code {n m d c : ℕ}
    (C : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
    (hcount : (3 * m) ^ d = c + 1) (initial : List (Row m))
    (hcode : ∀ v : Row m,
      (∀ r ∈ initial, (∑ e, r e * v e) = 0) → v ≠ 0 →
      m ≤ d * SparseCode.weight v) :
    ∀ x, accepts (cnfRowAccept C) initial x = true →
      0 < HashInput.violationWeight C x →
      3 * survivingCandidates (cnfRowAccept C) (tupleFamily hcount) x ≤
        2 * (c + 1) := by
  intro x hx hw
  apply tupleFamily_survival C hcount x hm
  rw [supportCard_eq_codeWeight]
  apply hcode
  · intro r hr
    have ha := List.all_eq_true.mp hx r hr
    simpa [cnfRowAccept] using ha
  · intro hv
    have hs := (HashInput.violationVector_eq_zero_iff (R := ZMod 3) C x).mp hv
    have hz := (HashInput.violationWeight_eq_zero_iff C x).mpr hs
    omega

/-- The only semantic assumptions left are the code distance and the exact
answers of the evaluator on the actual trial matrices. -/
theorem select_cnf_with_code {n m d c : ℕ}
    (C : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
    (hcount : (3 * m) ^ d = c + 1)
    (evaluate : List (Row m) → ℕ) (initial : List (Row m))
    (hcode : ∀ v : Row m,
      (∀ r ∈ initial, (∑ e, r e * v e) = 0) → v ≠ 0 →
      m ≤ d * SparseCode.weight v)
    (hsound : ∀ t < loopCap n m, ∀ i,
      evaluate (tupleFamily hcount i :: run evaluate (tupleFamily hcount) initial t) =
        mass (cnfRowAccept C) (HashInput.violationWeight C)
          (tupleFamily hcount i :: run evaluate (tupleFamily hcount) initial t)) :
    ∀ x, accepts (cnfRowAccept C)
      (run evaluate (tupleFamily hcount) initial (loopCap n m)) x = true ↔
      ∀ e, (C e).eval x = true :=
  select_cnf_correct C evaluate (tupleFamily hcount) initial hsound
    (initial_coverage_of_code C hm hcount initial hcode)

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionAlgebra

namespace OAI.Algorithms

/-! Explicit mixed-radix enumeration and deterministic maximal-minor scan.
The enumeration includes repeated indices; their zero determinants are harmless.
Its cost is counted separately from primitive-machine implementation. -/

namespace SubexponentialSAT.SqrtLog.RowSelection

structure Candidate (a b : ℕ) where
  size : ℕ
  rows : Fin size → Fin a
  cols : Fin size → Fin b

def Candidate.determinant {a b : ℕ} (c : Candidate a b)
    (P : Fin a → Fin b → ℤ) : ℤ := (minor P c.rows c.cols).det

def emptyCandidate (a b : ℕ) : Candidate a b := ⟨0, Fin.elim0, Fin.elim0⟩

@[simp] theorem emptyCandidate_size (a b : ℕ) : (emptyCandidate a b).size = 0 := rfl

@[simp] theorem emptyCandidate_det {a b : ℕ} (P : Fin a → Fin b → ℤ) :
    (emptyCandidate a b).determinant P = 1 := by
  change (minor P (Fin.elim0 : Fin 0 → Fin a) (Fin.elim0 : Fin 0 → Fin b)).det = 1
  exact Matrix.det_isEmpty

/-- Explicit tuple indexing, with no noncomputable finite enumeration. -/
def candidateAt (a b s : ℕ) (i : Fin (a^s * b^s)) : Candidate a b :=
  let pair := finProdFinEquiv.symm i
  ⟨s, (finFunctionFinEquiv : (Fin s → Fin a) ≃ Fin (a^s)).symm pair.1,
    (finFunctionFinEquiv : (Fin s → Fin b) ≃ Fin (b^s)).symm pair.2⟩

@[simp] theorem candidateAt_size (a b s : ℕ) (i : Fin (a^s*b^s)) :
    (candidateAt a b s i).size = s := rfl

theorem candidateAt_complete {a b s : ℕ} (rows : Fin s → Fin a)
    (cols : Fin s → Fin b) :
    ∃ i, candidateAt a b s i = ⟨s, rows, cols⟩ := by
  refine ⟨finProdFinEquiv (finFunctionFinEquiv rows, finFunctionFinEquiv cols), ?_⟩
  simp [candidateAt]

/-- Every size through K is examined, in increasing mixed-radix order. -/
def candidates (a b K : ℕ) : List (Candidate a b) :=
  (List.range (K+1)).flatMap fun s => List.ofFn (candidateAt a b s)

theorem candidate_mem {a b K s : ℕ} (hs : s ≤ K) (rows : Fin s → Fin a)
    (cols : Fin s → Fin b) : (⟨s, rows, cols⟩ : Candidate a b) ∈ candidates a b K := by
  obtain ⟨i, hi⟩ := candidateAt_complete rows cols
  apply List.mem_flatMap.mpr
  refine ⟨s, List.mem_range.mpr (by omega), ?_⟩
  exact List.mem_ofFn.mpr ⟨i, hi⟩

theorem size_le_of_mem_candidates {a b K : ℕ} {c : Candidate a b}
    (hc : c ∈ candidates a b K) : c.size ≤ K := by
  obtain ⟨s, hs, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  simpa using Nat.le_of_lt_succ (List.mem_range.mp hs)

/-- Preserve the earlier candidate on ties. -/
def choose {a b : ℕ} (P : Fin a → Fin b → ℤ) (old next : Candidate a b) :
    Candidate a b :=
  if next.determinant P ≠ 0 ∧ old.size < next.size then next else old

theorem choose_good {a b : ℕ} (P : Fin a → Fin b → ℤ) (old next : Candidate a b)
    (h : old.determinant P ≠ 0) : (choose P old next).determinant P ≠ 0 := by
  unfold choose
  split_ifs with hc
  · exact hc.1
  · exact h

theorem choose_ge_old {a b : ℕ} (P : Fin a → Fin b → ℤ) (old next : Candidate a b) :
    old.size ≤ (choose P old next).size := by
  unfold choose
  split_ifs with hc
  · exact hc.2.le
  · exact le_rfl

theorem choose_ge_next {a b : ℕ} (P : Fin a → Fin b → ℤ) (old next : Candidate a b)
    (h : next.determinant P ≠ 0) : next.size ≤ (choose P old next).size := by
  unfold choose
  split_ifs with hc
  · exact le_rfl
  · exact Nat.le_of_not_gt (fun hlt => hc ⟨h, hlt⟩)

theorem choose_le {a b K : ℕ} (P : Fin a → Fin b → ℤ) (old next : Candidate a b)
    (ho : old.size ≤ K) (hn : next.size ≤ K) : (choose P old next).size ≤ K := by
  unfold choose
  split_ifs <;> assumption

def scan {a b : ℕ} (P : Fin a → Fin b → ℤ) : List (Candidate a b) →
    Candidate a b → Candidate a b
  | [], old => old
  | next :: rest, old => scan P rest (choose P old next)

theorem scan_good {a b : ℕ} (P : Fin a → Fin b → ℤ) (cs : List (Candidate a b))
    (old : Candidate a b) (h : old.determinant P ≠ 0) :
    (scan P cs old).determinant P ≠ 0 := by
  induction cs generalizing old with
  | nil => exact h
  | cons c cs ih => exact ih _ (choose_good P old c h)

theorem scan_ge_old {a b : ℕ} (P : Fin a → Fin b → ℤ) (cs : List (Candidate a b))
    (old : Candidate a b) : old.size ≤ (scan P cs old).size := by
  induction cs generalizing old with
  | nil => exact le_rfl
  | cons c cs ih => exact (choose_ge_old P old c).trans (ih _)

theorem scan_ge_member {a b : ℕ} (P : Fin a → Fin b → ℤ)
    (cs : List (Candidate a b)) (old c : Candidate a b)
    (hc : c ∈ cs) (hgood : c.determinant P ≠ 0) : c.size ≤ (scan P cs old).size := by
  induction cs generalizing old with
  | nil => simp at hc
  | cons next rest ih =>
    rcases List.mem_cons.mp hc with rfl | hc
    · exact (choose_ge_next P old c hgood).trans (scan_ge_old P rest _)
    · exact ih _ hc

theorem scan_le {a b K : ℕ} (P : Fin a → Fin b → ℤ) (cs : List (Candidate a b))
    (old : Candidate a b) (h : old.size ≤ K) (hall : ∀ c ∈ cs, c.size ≤ K) :
    (scan P cs old).size ≤ K := by
  induction cs generalizing old with
  | nil => exact h
  | cons c cs ih =>
    exact ih _ (choose_le P old c h (hall _ (by simp)))
      (fun c hc => hall c (by simp [hc]))

def limit (a b cap : ℕ) : ℕ := min cap (min a b)

/-- Actual deterministic selection, depending only on the matrix and rank cap. -/
def select {a b : ℕ} (P : Fin a → Fin b → ℤ) (cap : ℕ) : Candidate a b :=
  scan P (candidates a b (limit a b cap)) (emptyCandidate a b)

theorem select_good {a b : ℕ} (P : Fin a → Fin b → ℤ) (cap : ℕ) :
    (select P cap).determinant P ≠ 0 :=
  scan_good P _ _ (by simp)

theorem select_le {a b : ℕ} (P : Fin a → Fin b → ℤ) (cap : ℕ) :
    (select P cap).size ≤ limit a b cap :=
  scan_le P _ _ (Nat.zero_le _) (fun _ hc => size_le_of_mem_candidates hc)

theorem select_maximal {a b s : ℕ} (P : Fin a → Fin b → ℤ) (cap : ℕ)
    (rows : Fin s → Fin a) (cols : Fin s → Fin b)
    (hs : s ≤ limit a b cap) (h : (minor P rows cols).det ≠ 0) :
    s ≤ (select P cap).size :=
  scan_ge_member P _ _ ⟨s, rows, cols⟩ (candidate_mem hs rows cols) h

end SubexponentialSAT.SqrtLog.RowSelection

end OAI.Algorithms

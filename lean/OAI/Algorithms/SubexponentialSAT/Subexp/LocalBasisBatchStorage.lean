import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPreparation

namespace OAI.Algorithms

/-!
# Storage operations for the physical local-basis batch

The batch reserves two disjoint work banks for matrix construction and local
search. These commands copy, clear, and serialize the actual words in those
banks; no matrix or basis is supplied by a semantic callback.
-/

namespace SubexponentialSAT.Subexp.LocalBasisBatchProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 32 128
abbrev Code := Cmd 32 128
abbrev Word := List Bool

def copyState (src dst : Fin 128) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks src dst a.stacks⟩

def copy (src dst : Fin 128) : Code := .call (copyProgram src dst 125 0 1)

theorem copy_eval (src dst : Fin 128) (a : Data)
    (hsd : src ≠ dst) (hst : src ≠ 125) (htd : (125 : Fin 128) ≠ dst)
    (ht : a.stacks 125 = []) :
    Eval (copy src dst) (7 * (a.stacks src).length + 5) a (copyState src dst a) :=
  TupleProgram.copy_eval src dst 125 0 1 hsd hst htd (by decide) a ht

@[simp] theorem copyState_frame (src dst j : Fin 128) (a : Data) (hj : j ≠ dst) :
    (copyState src dst a).stacks j = a.stacks j := by
  simp [copyState, copyStacks, hj]

def copyMany : List (Fin 128 × Fin 128) → Code
  | [] => .base .skip
  | (src, dst) :: rest => .seq (copy src dst) (copyMany rest)

def copyManyState : List (Fin 128 × Fin 128) → Data → Data
  | [], a => a
  | (src, dst) :: rest, a => copyManyState rest (copyState src dst a)

def copyManyCost : List (Fin 128 × Fin 128) → Data → ℕ
  | [], _ => 0
  | (src, dst) :: rest, a =>
      7 * (a.stacks src).length + 5 + copyManyCost rest (copyState src dst a)

theorem copyMany_eval (pairs : List (Fin 128 × Fin 128)) (a : Data)
    (hp : ∀ p ∈ pairs, p.1 ≠ p.2 ∧ p.1 ≠ 125 ∧ (125 : Fin 128) ≠ p.2)
    (ht : a.stacks 125 = []) :
    Eval (copyMany pairs) (copyManyCost pairs a) a (copyManyState pairs a) := by
  induction pairs generalizing a with
  | nil => exact .base (.skip a)
  | cons p ps ih =>
      rcases p with ⟨src, dst⟩
      have h := hp (src, dst) (by simp)
      have hr : ∀ p ∈ ps, p.1 ≠ p.2 ∧ p.1 ≠ 125 ∧ (125 : Fin 128) ≠ p.2 :=
        fun p hm => hp p (by simp [hm])
      have ht' : (copyState src dst a).stacks 125 = [] :=
        (copyState_frame src dst 125 a h.2.2).trans ht
      exact (copy_eval src dst a h.1 h.2.1 h.2.2 ht).seq (ih _ hr ht')

theorem copyMany_frame (pairs : List (Fin 128 × Fin 128)) (a : Data) (j : Fin 128)
    (hj : ∀ p ∈ pairs, j ≠ p.2) : (copyManyState pairs a).stacks j = a.stacks j := by
  induction pairs generalizing a with
  | nil => rfl
  | cons p ps ih =>
      rcases p with ⟨src, dst⟩
      exact (ih (copyState src dst a) (fun p hm => hj p (by simp [hm]))).trans
        (copyState_frame src dst j a (hj (src, dst) (by simp)))

def clearState (j : Fin 128) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, clearStacks j a.stacks⟩

def clear (j : Fin 128) : Code := .call (clearProgram j 0 1)

theorem clear_eval (j : Fin 128) (a : Data) :
    Eval (clear j) (2 * (a.stacks j).length + 3) a (clearState j a) :=
  TupleProgram.clear_eval j 0 1 a

def clearMany : List (Fin 128) → Code
  | [] => .base .skip
  | j :: rest => .seq (clear j) (clearMany rest)

def clearManyState : List (Fin 128) → Data → Data
  | [], a => a
  | j :: rest, a => clearManyState rest (clearState j a)

def clearManyCost : List (Fin 128) → Data → ℕ
  | [], _ => 0
  | j :: rest, a => 2 * (a.stacks j).length + 3 + clearManyCost rest (clearState j a)

theorem clearMany_eval (ports : List (Fin 128)) (a : Data) :
    Eval (clearMany ports) (clearManyCost ports a) a (clearManyState ports a) := by
  induction ports generalizing a with
  | nil => exact .base (.skip a)
  | cons j js ih => exact (clear_eval j a).seq (ih _)

theorem clearMany_stacks (ports : List (Fin 128)) (a : Data) (j : Fin 128) :
    (clearManyState ports a).stacks j = if j ∈ ports then [] else a.stacks j := by
  induction ports generalizing a with
  | nil => simp [clearManyState]
  | cons k ks ih =>
      rw [clearManyState, ih]
      by_cases hk : j = k <;> by_cases hs : j ∈ ks <;>
        simp [clearState, clearStacks, hk, hs]

def transferState (src dst : Fin 128) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, transferStacks src dst a.stacks⟩

def transfer (src dst : Fin 128) : Code := .call (transferProgram src dst 0 1)

theorem transfer_eval (src dst : Fin 128) (a : Data) (h : src ≠ dst) :
    Eval (transfer src dst) (3 * (a.stacks src).length + 3) a
      (transferState src dst a) :=
  TupleProgram.transfer_eval src dst 0 1 h (by decide) a

def move (src dst : Fin 128) : Code := .seq (transfer src 125) (transfer 125 dst)

def moved (src dst : Fin 128) (a : Data) : Data :=
  transferState 125 dst (transferState src 125 a)

theorem move_eval (src dst : Fin 128) (a : Data)
    (hs : src ≠ 125) (hd : (125 : Fin 128) ≠ dst) (ht : a.stacks 125 = []) :
    Eval (move src dst) (6 * (a.stacks src).length + 6) a (moved src dst a) := by
  have h0 := transfer_eval src 125 a hs
  have h1 := transfer_eval 125 dst (transferState src 125 a) hd
  have hl : ((transferState src 125 a).stacks 125).length = (a.stacks src).length := by
    simp [transferState, transferStacks, ht]
  rw [hl] at h1
  have h := h0.seq h1
  have hcost : 3 * (a.stacks src).length + 3 +
      (3 * (a.stacks src).length + 3) = 6 * (a.stacks src).length + 6 := by omega
  rw [hcost] at h
  exact h

theorem moved_stacks (src dst : Fin 128) (a : Data)
    (hs : src ≠ 125) (hd : dst ≠ 125) (hsd : src ≠ dst) (ht : a.stacks 125 = []) :
    (moved src dst a).stacks =
      Function.update (Function.update a.stacks src []) dst
        (a.stacks src ++ a.stacks dst) := by
  funext j
  by_cases hj : j = dst
  · subst j
    simp [moved, transferState, transferStacks, ht, hd, Ne.symm hsd]
  · by_cases hk : j = src
    · subst j
      simp [moved, transferState, transferStacks, ht, hs, hsd]
    · by_cases htmp : j = 125
      · subst j
        simp [moved, transferState, transferStacks, ht, hd, Ne.symm hs, Ne.symm hd]
      · simp [moved, transferState, transferStacks, hj, hk, htmp]

def reset : Code :=
  (List.finRange 32).foldr (fun j rest => .seq (.base (.atom (.set j false))) rest) (.base .skip)

end SubexponentialSAT.Subexp.LocalBasisBatchProgram

end OAI.Algorithms

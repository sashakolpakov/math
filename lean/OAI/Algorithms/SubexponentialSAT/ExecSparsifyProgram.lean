import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyNodeBranch
import OAI.Algorithms.SubexponentialSAT.ExecCNFNodeSearch

namespace OAI.Algorithms

/-!
# The closed finite program for one sparsification node

Every instruction table in this definition is concrete: bounded head
extraction, the record-count and width producer, the static width driver,
its index-and-mask loop, both child constructors, and both cleanup paths.
The single compile-time parameter is the clause-width bound k.
-/

namespace SubexponentialSAT.ExecSparsifyProgram

open BitProgram StructuredCalls
open ExecSparsifyNode

def searchPort (k : ℕ) (i : Fin (k + 34)) : Fin (k + 39) :=
  ⟨5 + i.val, by omega⟩

theorem searchPort_injective (k : ℕ) : Function.Injective (searchPort k) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 5 + i.val = 5 + j.val at hv
  omega

@[simp] theorem searchPort_low (k : ℕ) (i : Fin 32) :
    searchPort k (ExecCNFWidthLoad.low k i) = port k ⟨5 + i.val, by omega⟩ := rfl

def search (k : ℕ) : Code k :=
  .call (ProgramLinking.liftProgram (ExecCNFNodeSearch.program k) id (searchPort k))

def peekWitness (k : ℕ) : Code k := .base (.atom (.peek (port k 26) 0 1))

def peeked {k : ℕ} (a : Data k) : Data k :=
  (StructuredProgram.Atom.peek (port k 26) 0 1).eval a

@[simp] theorem peeked_stacks {k : ℕ} (a : Data k) : (peeked a).stacks = a.stacks := rfl

@[simp] theorem peeked_flag {k : ℕ} (a : Data k) :
    (peeked a).regs 1 = (a.stacks (port k 26)).head?.isSome :=
  readRegs_present a.regs 0 1 _

def finish (k : ℕ) : Code k :=
  .seq (peekWitness k) (.ite 1 (branch k) (terminalReturn k))

def command (k : ℕ) : Code k :=
  .seq (readHead k) (.seq (search k) (finish k))

def program (k : ℕ) := compiled (command k) (port k 0) (port k 2)

/-- A terminal search result is cleaned by actual instructions and sets the
outer worklist's terminal bit. No SAT predicate is consulted here. -/
theorem finish_terminal_eval {k : ℕ} (a : Data k)
    (h : a.stacks (port k 26) = []) :
    Eval (finish k) (terminalCost a + 2) a (terminalReturned a) := by
  have hf : (peeked a).regs 1 = false := by simp [h]
  have he : Eval (finish k) (1 + (terminalCost a + 1)) a (terminalReturned a) :=
    (show Eval (peekWitness k) 1 a (peeked a) from .base (.atom _ _)).seq
      (Eval.ite_false (yes := branch k) hf (terminalReturn_eval (peeked a)))
  have htime : 1 + (terminalCost a + 1) = terminalCost a + 2 := by omega
  exact htime ▸ he

/-- A successful search result invokes the two concrete child programs.
The retained witness's existence is checked by the real peek instruction. -/
theorem finish_branch_eval {k : ℕ} (a : Data k)
    (F selected : List (List ℕ)) (H : List ℕ)
    (hw : a.stacks (port k 26) ≠ [])
    (h2 : a.stacks (port k 2) = []) (h3 : a.stacks (port k 3) = [])
    (h4 : a.stacks (port k 4) = []) (h5 : a.stacks (port k 5) = [])
    (h6 : a.stacks (port k 6) = []) (h7 : a.stacks (port k 7) = [])
    (hF : a.stacks (port k 21) = ExecBranchController.formulaCode F)
    (hS : a.stacks (port k 18) = ExecBranchController.formulaCode selected)
    (hH : a.stacks (port k 13) = ExecBranchController.clauseCode H) :
    ∃ t ≤ branchCost a F selected H + 2,
      Eval (finish k) t a (branchProduced (peeked a) F selected H) := by
  have hf : (peeked a).regs 1 = true := by
    rw [peeked_flag]
    cases hword : a.stacks (port k 26) <;> simp_all
  obtain ⟨t, ht, he⟩ := branch_eval (peeked a) F selected H h2 h3 h4 h5 h6 h7 hF hS hH
  refine ⟨1 + (t + 1), ?_, ?_⟩
  · have hc : branchCost (peeked a) F selected H = branchCost a F selected H := rfl
    rw [hc] at ht
    omega
  · exact (show Eval (peekWitness k) 1 a (peeked a) from .base (.atom _ _)).seq
      (Eval.ite_true (no := terminalReturn k) hf he)

end SubexponentialSAT.ExecSparsifyProgram

end OAI.Algorithms

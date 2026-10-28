import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleSplit

namespace OAI.Algorithms

/-!
# Saving the first accepted encoded candidate

The witness lives on stack 21, so it survives the tuple controller's register
updates. This fixed program peeks that stack and copies the complete candidate
from stack 17 only when the witness is empty and acceptance register 17 is true.
Every other stack, including the materialized core and family, is preserved.
-/

namespace SubexponentialSAT.ExecCNFFirstWitness

open BitProgram StructuredCalls

abbrev Data := State 32 32
abbrev Code := Cmd 32 32

def peek : Code := .base (.atom (.peek 21 0 1))

def peeked (d : Data) : Data := (StructuredProgram.Atom.peek 21 0 1).eval d

def command : Code :=
  .seq peek (.ite 1 (.base .skip)
    (.ite 17 (ExecCNFTupleSplit.copy 17 21) (.base .skip)))

def program := compiled command 17 21

/-- The mathematical update effected by the actual finite command. -/
def save (candidate witness : List Bool) (accepted : Bool) : List Bool :=
  if witness = [] ∧ accepted = true then candidate else witness

def result (d : Data) : Data :=
  if d.stacks 21 = [] ∧ d.regs 17 = true then
    ExecCNFTupleSplit.copied 17 21 (peeked d)
  else peeked d

def cost (d : Data) : ℕ :=
  if d.stacks 21 = [] then
    if d.regs 17 = true then 7 * (d.stacks 17).length + 8 else 3
  else 2

@[simp] theorem peeked_stacks (d : Data) : (peeked d).stacks = d.stacks := rfl

theorem peeked_register_frame (d : Data) (i : Fin 32) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    (peeked d).regs i = d.regs i :=
  StackRoutines.readRegs_frame d.regs 0 1 i (d.stacks 21).head? h0 h1

@[simp] theorem peeked_accept (d : Data) : (peeked d).regs 17 = d.regs 17 :=
  peeked_register_frame d 17 (by decide) (by decide)

@[simp] theorem peeked_present (d : Data) :
    (peeked d).regs 1 = (d.stacks 21).head?.isSome := by
  exact readRegs_present d.regs 0 1 _

theorem result_witness (d : Data) :
    (result d).stacks 21 = save (d.stacks 17) (d.stacks 21) (d.regs 17) := by
  by_cases h : d.stacks 21 = [] ∧ d.regs 17 = true
  · simp [result, save, h, ExecCNFTupleSplit.copied, StackRoutines.copyStacks ]
  · simp [result, save, h]

theorem result_stack_frame (d : Data) (i : Fin 32) (h : i ≠ 21) :
    (result d).stacks i = d.stacks i := by
  by_cases hc : d.stacks 21 = [] ∧ d.regs 17 = true
  · simp only [result, ite_eq_left hc]
    exact (ExecCNFTupleSplit.copied_stack_frame 17 21 (peeked d) i h).trans rfl
  · simp [result, hc]

theorem result_register_frame (d : Data) (i : Fin 32) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    (result d).regs i = d.regs i := by
  by_cases hc : d.stacks 21 = [] ∧ d.regs 17 = true
  · simp only [result, ite_eq_left hc, ExecCNFTupleSplit.copied]
    exact (StackRoutines.readRegs_frame (peeked d).regs 0 1 i none h0 h1).trans
      (peeked_register_frame d i h0 h1)
  · simpa only [result, ite_eq_right hc] using peeked_register_frame d i h0 h1

/-- This counts the initial peek, both relevant branch tests, and the actual
source-preserving copy, with its scratch restoration and return instruction. -/
theorem command_eval (d : Data) (h25 : d.stacks 25 = []) :
    Eval command (cost d) d (result d) := by
  have hp : Eval peek 1 d (peeked d) := .base (.atom _ _)
  cases hw : d.stacks 21 with
  | nil =>
    have hflag : (peeked d).regs 1 = false := by simp [hw]
    cases ha : d.regs 17 with
    | false =>
      have hr : Eval (.ite 1 (.base .skip)
          (.ite 17 (ExecCNFTupleSplit.copy 17 21) (.base .skip))) 2
          (peeked d) (peeked d) :=
        .ite_false hflag (.ite_false (by simpa using ha) (.base (.skip _)))
      simpa [command, result, cost, hw, ha] using Eval.seq hp hr
    | true =>
      have hc := ExecCNFTupleSplit.copy_eval 17 21 (peeked d)
        (by decide) (by decide) (by decide) h25
      have hr := Eval.ite_false (yes := .base .skip) hflag
        (Eval.ite_true (test := 17) (no := .base .skip) (by simpa using ha) hc)
      have ht : 1 + ((7 * (d.stacks 17).length + 5 + 1) + 1) =
          7 * (d.stacks 17).length + 8 := by omega
      simpa only [command, result, hw, ha, and_self, ite_true, cost,
        peeked_stacks, ht] using Eval.seq hp hr
  | cons bit tail =>
    have hflag : (peeked d).regs 1 = true := by simp [hw]
    have hr := Eval.ite_true
      (no := .ite 17 (ExecCNFTupleSplit.copy 17 21) (.base .skip))
      hflag (show Eval (.base .skip) 0 (peeked d) (peeked d) from .base (.skip _))
    simpa [command, result, cost, hw] using Eval.seq hp hr

theorem cost_le (d : Data) : cost d ≤ 7 * (d.stacks 17).length + 8 := by
  unfold cost
  split_ifs <;> omega

/-- A previously saved witness is never overwritten, including when a later
candidate is also accepted. -/
theorem result_preserves_saved (d : Data) (h : d.stacks 21 ≠ []) :
    (result d).stacks 21 = d.stacks 21 := by
  rw [result_witness]
  simp [save, h]

theorem result_commits (d : Data) (h : d.stacks 21 = []) (ha : d.regs 17 = true) :
    (result d).stacks 21 = d.stacks 17 := by
  rw [result_witness]
  simp [save, h, ha]

theorem result_rejects (d : Data) (ha : d.regs 17 = false) :
    (result d).stacks 21 = d.stacks 21 := by
  rw [result_witness]
  simp [save, ha]

theorem save_nonempty_iff (candidate witness : List Bool) (accepted : Bool)
    (hc : candidate ≠ []) :
    save candidate witness accepted ≠ [] ↔ witness ≠ [] ∨ accepted = true := by
  unfold save
  split_ifs with h
  · simp [h.2, hc]
  · cases ha : accepted
    · simp []
    · have hw : witness ≠ [] := by intro hw; exact h ⟨hw, ha⟩
      simp [hw]

/-- The fixed command has eleven source labels and one final halt. -/
theorem command_size : size command = 11 := rfl

theorem program_runs (d : Data) (h25 : d.stacks 25 = []) :
    RunsIn program (7 * (d.stacks 17).length + 9)
      (d.withPC (some program.entry)) ((result d).withPC none) :=
  ⟨cost d + 1, by have := cost_le d; omega,
    compiled_halt_trace (command_eval d h25) 17 21⟩

theorem program_primitive (d : Data) (h25 : d.stacks 25 = []) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (7 * (d.stacks 17).length + 9))
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program ((result d).withPC none)) :=
  BitProgram.primitive_execution program (program_runs d h25)

end SubexponentialSAT.ExecCNFFirstWitness

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ParserProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace OAI.Algorithms

/-!
# Concrete preparation of a mask-first candidate tuple

The full tuple remains on stack 17. This fixed program puts the forward-order
mask on 22 and the unchanged encoded index list on 23, clearing scratch 24--26.
All copies, parsing, reversal, and cleanup are actual finite subroutine calls.
-/

namespace SubexponentialSAT.ExecCNFTupleSplit

open BitProgram StructuredCalls

abbrev Data := State 32 32
abbrev Code := Cmd 32 32

def copied (src dst : Fin 32) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

def copy (src dst : Fin 32) : Code := .call (StackRoutines.copyProgram src dst 25 0 1)

theorem copy_eval (src dst : Fin 32) (d : Data)
    (hsd : src ≠ dst) (hst : src ≠ 25) (hdt : dst ≠ 25) (h25 : d.stacks 25 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied src dst d) := by
  have ht := StackRoutines.copyProgram_trace src dst 25 (0 : Fin 32) 1
    hsd hst hdt.symm (by decide) d.regs d.stacks h25
  have hh := StackRoutines.halt_after_trace _ ht 7 rfl rfl
  apply Eval.call
  simpa [copied, StackRoutines.copyResult, StackRoutines.copyProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using hh

def cleared (src : Fin 32) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks src d.stacks⟩

def clear (src : Fin 32) : Code := .call (StackRoutines.clearProgram src 0 1)

theorem clear_eval (src : Fin 32) (d : Data) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared src d) := by
  have ht := StackRoutines.clearProgram_trace src (0 : Fin 32) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ ht 2 rfl rfl
  apply Eval.call
  simpa [cleared, StackRoutines.clearResult, StackRoutines.clearProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using hh

def reversed (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.reverseStacks 22 d.stacks⟩

def reverseMask : Code := .call (StackRoutines.reverseProgram 22 25 26 0 1)

theorem reverseMask_eval (d : Data) (h25 : d.stacks 25 = []) (h26 : d.stacks 26 = []) :
    Eval reverseMask (9 * (d.stacks 22).length + 7) d (reversed d) := by
  have ht := StackRoutines.reverseProgram_trace (22 : Fin 32) 25 26 (0 : Fin 32) 1
    (by decide) (by decide) (by decide) (by decide) d.regs d.stacks h25 h26
  have hh := StackRoutines.halt_after_trace _ ht 9 rfl rfl
  apply Eval.call
  simpa [reversed, StackRoutines.reverseResult, StackRoutines.reverseProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using hh

def parseReg (i : Fin 2) : Fin 32 := Fin.castAdd 30 i
def parseStack (i : Fin 2) : Fin 32 := if i = 0 then 24 else 22

theorem parseReg_injective : Function.Injective parseReg := Fin.castAdd_injective 2 30

theorem parseStack_injective : Function.Injective parseStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [parseStack]

def parseMask : Code :=
  .call (ProgramLinking.liftProgram ParserProgram.frameProgram parseReg parseStack)

noncomputable def parsed (d : Data) (mask rest : List Bool) : Data :=
  embedState parseReg parseStack d ⟨ParserProgram.pair false true, ParserProgram.pair rest mask.reverse⟩

theorem parseMask_eval (d : Data) (mask rest : List Bool)
    (h24 : d.stacks 24 = Encoding.frame mask ++ rest) (h22 : d.stacks 22 = []) :
    Eval parseMask (6 * mask.length + 4) d (parsed d mask rest) := by
  have ht := ParserProgram.frame_trace mask rest [] (d.regs 0) (d.regs 1)
  have hp : projectState parseReg parseStack d =
      ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
        ParserProgram.pair (Encoding.frame mask ++ rest) []⟩ := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [ parseStack, h24, h22]
  apply eval_call_from_state _ parseReg parseStack d parseReg_injective parseStack_injective
  rw [hp]
  simpa [ParserProgram.cfg, StructuredProgram.State.withPC] using ht

@[simp] theorem parsed_mask (d : Data) (mask rest : List Bool) :
    (parsed d mask rest).stacks 22 = mask.reverse := by
  exact embedState_stack _ _ _ _ parseStack_injective 1

@[simp] theorem parsed_rest (d : Data) (mask rest : List Bool) :
    (parsed d mask rest).stacks 24 = rest := by
  exact embedState_stack _ _ _ _ parseStack_injective 0

theorem parsed_stack_frame (d : Data) (mask rest : List Bool) (i : Fin 32)
    (h22 : i ≠ 22) (h24 : i ≠ 24) : (parsed d mask rest).stacks i = d.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j, hj⟩
  fin_cases j <;> simp [parseStack] at hj
  · exact h24 hj.symm
  · exact h22 hj.symm

def popTag : Code := .base (.atom (.pop 24 0 1))
abbrev popped (d : Data) : Data := (StructuredProgram.Atom.pop 24 0 1).eval d

def command : Code :=
  .seq (copy 17 24) (.seq popTag (.seq parseMask
    (.seq reverseMask (.seq (copy 24 23) (clear 24)))))

abbrev program := compiled command 17 22

def Ready (mask : List Bool) (indices : List (List Bool)) (d : Data) : Prop :=
  d.stacks 17 = Encoding.encodeList id (mask :: indices) ∧
  d.stacks 22 = [] ∧ d.stacks 23 = [] ∧ d.stacks 24 = [] ∧
  d.stacks 25 = [] ∧ d.stacks 26 = []

theorem copied_stack_frame (src dst : Fin 32) (d : Data) (i : Fin 32) (hi : i ≠ dst) :
    (copied src dst d).stacks i = d.stacks i :=
  StackRoutines.copyStacks_frame src dst i d.stacks hi

theorem cleared_stack_frame (src : Fin 32) (d : Data) (i : Fin 32) (hi : i ≠ src) :
    (cleared src d).stacks i = d.stacks i :=
  StackRoutines.clearStacks_frame src i d.stacks hi

theorem reversed_stack_frame (d : Data) (i : Fin 32) (hi : i ≠ 22) :
    (reversed d).stacks i = d.stacks i := by
  simp [reversed, StackRoutines.reverseStacks, hi]

theorem popped_stack_frame (d : Data) (i : Fin 32) (hi : i ≠ 24) :
    (popped d).stacks i = d.stacks i := by
  simp [popped, StructuredProgram.Atom.eval, StructuredProgram.State.ofCfg,
    StructuredProgram.Atom.instr, execInstr, hi]

def cost (mask : List Bool) (indices : List (List Bool)) : ℕ :=
  7 * (Encoding.encodeList id (mask :: indices)).length + 15 * mask.length +
    9 * (Encoding.encodeList id indices).length + 25

/-- Exact measured composition: forward mask and index-list outputs, source
tuple preserved, and all unrelated stacks framed. -/
theorem command_eval (mask : List Bool) (indices : List (List Bool)) (d : Data)
    (h : Ready mask indices d) :
    ∃ e, Eval command (cost mask indices) d e ∧
      e.stacks 22 = mask ∧ e.stacks 23 = Encoding.encodeList id indices ∧ e.stacks 24 = [] ∧
      (∀ i : Fin 32, i ≠ 22 → i ≠ 23 → i ≠ 24 → e.stacks i = d.stacks i) := by
  rcases h with ⟨h17, h22, h23, h24, h25, h26⟩
  let a := copied 17 24 d
  let b := popped a
  let c := parsed b mask (Encoding.encodeList id indices)
  let e := reversed c
  let f := copied 24 23 e
  let g := cleared 24 f
  have ha24 : a.stacks 24 = Encoding.encodeList id (mask :: indices) := by
    simp [a, copied, StackRoutines.copyStacks, h17, h24]
  have hb24 : b.stacks 24 = Encoding.frame mask ++ Encoding.encodeList id indices := by
    change (a.stacks 24).tail = _
    rw [ha24]
    rfl
  have hb22 : b.stacks 22 = [] := by
    exact (popped_stack_frame a 22 (by decide)).trans
      ((copied_stack_frame 17 24 d 22 (by decide)).trans h22)
  have hc25 : c.stacks 25 = [] := by
    exact (parsed_stack_frame b mask _ 25 (by decide) (by decide)).trans
      ((popped_stack_frame a 25 (by decide)).trans
        ((copied_stack_frame 17 24 d 25 (by decide)).trans h25))
  have hc26 : c.stacks 26 = [] := by
    exact (parsed_stack_frame b mask _ 26 (by decide) (by decide)).trans
      ((popped_stack_frame a 26 (by decide)).trans
        ((copied_stack_frame 17 24 d 26 (by decide)).trans h26))
  have he25 : e.stacks 25 = [] := (reversed_stack_frame c 25 (by decide)).trans hc25
  have he22 : e.stacks 22 = mask := by
    simp [e, reversed, StackRoutines.reverseStacks, c]
  have he24 : e.stacks 24 = Encoding.encodeList id indices :=
    (reversed_stack_frame c 24 (by decide)).trans (parsed_rest b mask _)
  have he23 : e.stacks 23 = [] := by
    exact (reversed_stack_frame c 23 (by decide)).trans
      ((parsed_stack_frame b mask _ 23 (by decide) (by decide)).trans
        ((popped_stack_frame a 23 (by decide)).trans
          ((copied_stack_frame 17 24 d 23 (by decide)).trans h23)))
  have hf24 : f.stacks 24 = Encoding.encodeList id indices :=
    (copied_stack_frame 24 23 e 24 (by decide)).trans he24
  have hcopy := copy_eval 17 24 d (by decide) (by decide) (by decide) h25
  have hpop : Eval popTag 1 a b := .base (.atom _ _)
  have hparse := parseMask_eval b mask _ hb24 hb22
  have hreverse := reverseMask_eval c hc25 hc26
  have hindices := copy_eval 24 23 e (by decide) (by decide) (by decide) he25
  have hclear := clear_eval 24 f
  have hrun := Eval.seq hcopy (Eval.seq hpop (Eval.seq hparse
    (Eval.seq hreverse (Eval.seq hindices hclear))))
  have hc22 : c.stacks 22 = mask.reverse := parsed_mask b mask _
  have ht : (7 * (d.stacks 17).length + 5) +
      (1 + ((6 * mask.length + 4) + ((9 * (c.stacks 22).length + 7) +
        ((7 * (e.stacks 24).length + 5) + (2 * (f.stacks 24).length + 3))))) =
      cost mask indices := by
    rw [h17, hc22, he24, hf24]
    simp only [List.length_reverse, cost]
    omega
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [command, ht] using hrun
  · exact (cleared_stack_frame 24 f 22 (by decide)).trans
      ((copied_stack_frame 24 23 e 22 (by decide)).trans he22)
  · calc
      g.stacks 23 = f.stacks 23 := cleared_stack_frame 24 f 23 (by decide)
      _ = e.stacks 24 ++ e.stacks 23 := by simp [f, copied, StackRoutines.copyStacks]
      _ = Encoding.encodeList id indices := by rw [he24, he23, List.append_nil]
  · simp [g, cleared, StackRoutines.clearStacks]
  · intro i hi22 hi23 hi24
    exact (cleared_stack_frame 24 f i hi24).trans
      ((copied_stack_frame 24 23 e i hi23).trans
        ((reversed_stack_frame c i hi22).trans
          ((parsed_stack_frame b mask _ i hi22 hi24).trans
            ((popped_stack_frame a i hi24).trans (copied_stack_frame 17 24 d i hi24)))))

theorem cost_le_linear (mask : List Bool) (indices : List (List Bool)) :
    cost mask indices ≤ 16 * (Encoding.encodeList id (mask :: indices)).length + 7 := by
  simp only [cost, Encoding.length_encodeList_cons, id_eq]
  omega

theorem program_runs (mask : List Bool) (indices : List (List Bool)) (d : Data)
    (h : Ready mask indices d) :
    ∃ e : Data, RunsIn program (16 * (Encoding.encodeList id (mask :: indices)).length + 8)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks 22 = mask ∧ e.stacks 23 = Encoding.encodeList id indices ∧ e.stacks 24 = [] ∧
      (∀ i : Fin 32, i ≠ 22 → i ≠ 23 → i ≠ 24 → e.stacks i = d.stacks i) := by
  obtain ⟨e, he, h22, h23, h24, hf⟩ := command_eval mask indices d h
  exact ⟨e, ⟨cost mask indices + 1, by have := cost_le_linear mask indices; omega,
    compiled_halt_trace he 17 22⟩, h22, h23, h24, hf⟩

theorem program_primitive (mask : List Bool) (indices : List (List Bool)) (d : Data)
    (h : Ready mask indices d) :
    ∃ e : Data, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (16 * (Encoding.encodeList id (mask :: indices)).length + 8))
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) ∧
      e.stacks 22 = mask ∧ e.stacks 23 = Encoding.encodeList id indices ∧ e.stacks 24 = [] ∧
      (∀ i : Fin 32, i ≠ 22 → i ≠ 23 → i ≠ 24 → e.stacks i = d.stacks i) := by
  obtain ⟨e, he, h22, h23, h24, hf⟩ := program_runs mask indices d h
  exact ⟨e, BitProgram.primitive_execution program he, h22, h23, h24, hf⟩

end SubexponentialSAT.ExecCNFTupleSplit

end OAI.Algorithms

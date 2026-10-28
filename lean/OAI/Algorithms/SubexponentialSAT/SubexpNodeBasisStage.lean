import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisProgram
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWideLoop
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Physical static-input staging for the current-node basis producer. -/

namespace SubexponentialSAT.SubexpNodeBasisStage

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 288
abbrev Move := Fin 288 × Fin 288

def ports (i : Fin 64) : Fin 288 := ⟨138 + i.val, by omega⟩
theorem ports_injective : Function.Injective ports := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [ports] at hv
  omega

def moves : List Move :=
  [(116,170), (269,171), (266,175), (261,176), (264,184), (270,185),
    (271,186), (272,187), (276,151), (282,152), (283,153)]

def copies : List Move → Cmd 16 288
  | [] => .base .skip
  | (src,dst) :: rest =>
      .seq (.call (StackRoutines.copyProgram src dst 0 0 1)) (copies rest)

def copied : List Move → Data → Data
  | [], d => d
  | (src,dst) :: rest, d => copied rest (afterCopy d src dst 0 1)

def copyCost : List Move → Data → ℕ
  | [], _ => 0
  | (src,dst) :: rest, d => 7 * (d.stacks src).length + 5 +
      copyCost rest (afterCopy d src dst 0 1)

theorem copies_eval (ms : List Move) (d : Data) (h0 : d.stacks 0 = [])
    (hd : ∀ m ∈ ms, m.1 ≠ m.2 ∧ m.1 ≠ 0 ∧ m.2 ≠ 0) :
    Eval (copies ms) (copyCost ms d) d (copied ms d) := by
  induction ms generalizing d with
  | nil => exact .base (.skip d)
  | cons m ms ih =>
    rcases m with ⟨src,dst⟩
    have hh := hd (src,dst) (by simp)
    have hc := copy_eval d src dst 0 0 1 hh.1 hh.2.1 hh.2.2.symm (by decide) h0
    have hz : (afterCopy d src dst 0 1).stacks 0 = [] := by
      simpa [afterCopy, StackRoutines.copyStacks, hh.2.2.symm] using h0
    exact hc.seq (ih _ hz (by intro m hm; exact hd m (by simp [hm])))

theorem copied_frame (ms : List Move) (d : Data) (i : Fin 288)
    (hi : ∀ m ∈ ms, i ≠ m.2) : (copied ms d).stacks i = d.stacks i := by
  induction ms generalizing d with
  | nil => rfl
  | cons m ms ih =>
    rcases m with ⟨src,dst⟩
    rw [copied, ih _ (by intro m hm; exact hi m (by simp [hm]))]
    simp [afterCopy, StackRoutines.copyStacks, hi (src,dst) (by simp)]

abbrev prepare : Cmd 16 288 := copies moves

theorem prepare_eval (d : Data) (h0 : d.stacks 0 = []) :
    Eval prepare (copyCost moves d) d (copied moves d) := by
  apply copies_eval moves d h0
  intro m hm
  simp only [moves, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

abbrev clear (i : Fin 288) : Cmd 16 288 := .call (StackRoutines.clearProgram i 0 1)
def clearOut (d : Data) (i : Fin 288) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks i []⟩

theorem clear_eval (d : Data) (i : Fin 288) :
    Eval (clear i) (2 * (d.stacks i).length + 3) d (clearOut d i) := by
  exact .call _ (ListRegisterProgram.clear_run i 0 1 d.regs d.stacks)

def clears : List (Fin 288) → Cmd 16 288
  | [] => .base .skip
  | i :: is => .seq (clear i) (clears is)
def cleared : List (Fin 288) → Data → Data
  | [], d => d
  | i :: is, d => cleared is (clearOut d i)
def clearCost : List (Fin 288) → Data → ℕ
  | [], _ => 0
  | i :: is, d => 2 * (d.stacks i).length + 3 + clearCost is (clearOut d i)

theorem clears_eval (is : List (Fin 288)) (d : Data) :
    Eval (clears is) (clearCost is d) d (cleared is d) := by
  induction is generalizing d with
  | nil => exact .base (.skip d)
  | cons i is ih => exact (clear_eval d i).seq (ih _)

def workspace : List (Fin 288) := moves.map Prod.snd
abbrev call : Cmd 16 288 :=
  .call (ProgramLinking.liftProgram Subexp.GlobalBasisProgram.program id ports)
abbrev command : Cmd 16 288 := .seq prepare (.seq call (clears workspace))
abbrev program : Program 16 288 (size command + 1) := compiled command 116 201

/-- This adapter performs the actual input copies and cleanup. The native
producer's execution remains explicit until its independent proof is linked. -/
theorem program_trace_from_native (d : Data) (h0 : d.stacks 0 = [])
    (n : ℕ) (out : Subexp.GlobalBasisProgram.Data)
    (h : Trace Subexp.GlobalBasisProgram.program n
      ((projectState id ports (copied moves d)).withPC
        (some Subexp.GlobalBasisProgram.program.entry)) (out.withPC none)) :
    let e := embedState id ports (copied moves d) out
    Trace program (copyCost moves d + (n + clearCost workspace e) + 1)
      (d.withPC (some program.entry)) ((cleared workspace e).withPC none) := by
  have hc := eval_call_from_state Subexp.GlobalBasisProgram.program id ports
    (copied moves d) Function.injective_id ports_injective h
  exact compiled_halt_trace ((prepare_eval d h0).seq (hc.seq (clears_eval workspace _))) 116 201

theorem cleanup_output (d : Data) : (cleared workspace d).stacks 201 = d.stacks 201 := by
  simp [workspace, moves, cleared, clearOut]

end SubexponentialSAT.SubexpNodeBasisStage

end OAI.Algorithms

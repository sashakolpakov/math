import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWideSetup
import OAI.Algorithms.SubexponentialSAT.SubexpNodeSlotStage

namespace OAI.Algorithms

/-!
# Initialize the node workspace from the actual static dimension

Static264 is Main's generated unary dimension. The program copies it to109,
executes the concrete local and node-table setup, then constructs the retained
slot master with the actual slot generator. Every output is written by code.
-/

namespace SubexponentialSAT.SubexpNodeWideInitialization

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpNodeWideSetup (Data lowPorts lowPorts_injective lowState)

abbrev dimension : Cmd 16 352 :=
  .seq (SubexpNodeWideLoop.clear 109) (SubexpNodeWideLoop.copy 264 109)

def dimensionResult (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks 109 (d.stacks 264)⟩

def dimensionCost (d : Data) : ℕ :=
  2 * (d.stacks 109).length + 7 * (d.stacks 264).length + 8

theorem dimension_eval (d : Data) (htmp : d.stacks 337 = []) :
    Eval dimension (dimensionCost d) d (dimensionResult d) := by
  let a := SubexpNodeWideLoop.clearOut d 109
  have hc := SubexpNodeWideLoop.clear_eval d 109
  have hp := copy_eval a 264 109 337 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simpa [a, SubexpNodeWideLoop.clearOut] using htmp)
  have hs : afterCopy a 264 109 0 1 = dimensionResult d := by
    apply state_ext
    · simp [a, SubexpNodeWideLoop.clearOut, afterCopy, dimensionResult,
        StackRoutines.readRegs_reset]
    · simp [a, SubexpNodeWideLoop.clearOut, afterCopy, dimensionResult,
        StackRoutines.copyStacks]
  rw [hs] at hp
  convert hc.seq hp using 1 <;>
    simp [dimension, dimensionCost, SubexpNodeWideLoop.copy, a,
      SubexpNodeWideLoop.clearOut]
  all_goals omega

structure Ready (d : Data) : Prop where
  empty0 : d.stacks 0 = []
  empty1 : d.stacks 1 = []
  empty4 : d.stacks 4 = []
  exponent : ∀ i ∈ SubexpNodeExponentMaster.work, (lowState d).stacks i = []
  literal : SubexpNodeRawConstants.WorkEmpty (lowState d)
  zero : d.stacks 122 = []
  one : d.stacks 123 = []
  scalar : d.stacks 124 = []
  width : 0 < (d.stacks 10).length
  temporary : d.stacks 337 = []
  slots : SubexpNodeSlotStage.Ready (lowState d)

theorem dimension_ready (d : Data) (D : ℕ) (hr : Ready d)
    (hD : d.stacks 264 = List.replicate D true) :
    SubexpNodeWideSetup.Ready (dimensionResult d) D := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [dimensionResult] using hD
  · simpa [dimensionResult] using hr.empty0
  · simpa [dimensionResult] using hr.empty1
  · simpa [dimensionResult] using hr.empty4
  · intro i hi
    have hn : lowPorts i ≠ 109 := by
      simp only [SubexpNodeExponentMaster.work, List.mem_cons, List.mem_nil_iff,
        or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [lowState, projectState, dimensionResult, hn] using hr.exponent i hi
  · intro i hi hj
    have hn : lowPorts i ≠ 109 := by
      intro h
      have hv := congrArg Fin.val h
      change i.val = 109 at hv
      omega
    simpa [lowState, projectState, dimensionResult, hn] using hr.literal i hi hj
  · simpa [dimensionResult] using hr.zero
  · simpa [dimensionResult] using hr.one
  · simpa [dimensionResult] using hr.scalar
  · simpa [dimensionResult] using hr.width
  · simpa [dimensionResult] using hr.temporary

abbrev setup : Cmd 16 352 := .call SubexpNodeWideSetup.program
abbrev slots : Cmd 16 352 :=
  .call (ProgramLinking.liftProgram SubexpNodeSlotStage.program id lowPorts)
abbrev command : Cmd 16 352 := .seq dimension (.seq setup slots)

def resultStacks (d : Data) (D : ℕ) : Fin 352 → List Bool :=
  Function.update (SubexpNodeWideSetup.resultStacks (dimensionResult d) D)
    25 (SubexpSlotSetup.output D)

def slotBound (d : Data) (D : ℕ) : ℕ :=
  SubexpCompleteSlotSetup.bound D + 9 * D + 8 * SubexpSymbolicCost.indexBits D +
    6 * (SubexpSlotSetup.output D).length + 2 * (d.stacks 25).length + 27

def budget (d : Data) (D : ℕ) : ℕ := dimensionCost d +
  (SubexpNodeWideSetup.budget (dimensionResult d) D + 1 + slotBound d D)

private theorem setup_slots_ready (d e : Data) (D : ℕ) (hr : Ready d)
    (hs : e.stacks = SubexpNodeWideSetup.resultStacks (dimensionResult d) D) :
    SubexpNodeSlotStage.Ready (lowState e) := by
  have hf (i : Fin 256) (hi : 138 ≤ i.val) :
      (lowState e).stacks i = (lowState d).stacks i := by
    have hn (j : Fin 352) (hj : j.val < 138) : lowPorts i ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      change i.val = j.val at hv
      omega
    simp [lowState, projectState, hs, SubexpNodeWideSetup.resultStacks,
      SubexpNodeWideSetup.localResult, dimensionResult, hn 92 (by decide),
      hn 109 (by decide), hn 122 (by decide), hn 123 (by decide),
      hn 124 (by decide), hn 125 (by decide), hn 127 (by decide)]
  refine ⟨(hf 140 (by decide)).trans hr.slots.dimensionEmpty,
    (hf 139 (by decide)).trans hr.slots.temporaryEmpty,
    (hf 141 (by decide)).trans hr.slots.widthEmpty, ?_⟩
  intro i hi
  rw [hf (SubexpNodeJobsStage.port i) (by
    simp only [SubexpSlotSetup.work, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  exact hr.slots.workEmpty i hi

theorem command_eval (d : Data) (D : ℕ) (hr : Ready d)
    (hD : d.stacks 264 = List.replicate D true) :
    ∃ n ≤ budget d D, ∃ out : Data, Eval command n d out ∧
      out.stacks = resultStacks d D := by
  have hd := dimension_eval d hr.temporary
  obtain ⟨e, ⟨n, hn, ht⟩, hs⟩ := SubexpNodeWideSetup.program_runs (dimensionResult d) D
    (dimension_ready d D hr hD)
  have hED : (lowState e).stacks 109 = List.replicate D true := by
    simp [lowState, projectState, lowPorts, hs, SubexpNodeWideSetup.resultStacks,
      SubexpNodeWideSetup.localResult, dimensionResult, hD]
  obtain ⟨f, ⟨m, hm, htf⟩, hfs⟩ := SubexpNodeSlotStage.program_runs D (lowState e)
    hED (setup_slots_ready d e D hr hs)
  let out := embedState id lowPorts e f
  have he := eval_call_from_state _ _ _ _ Function.injective_id lowPorts_injective htf
  have hm' : m ≤ slotBound d D := by
    have hb : SubexpNodeSlotStage.bound D (lowState e) = slotBound d D := by
      simp [SubexpNodeSlotStage.bound, slotBound, lowState, projectState, lowPorts,
        hs, SubexpNodeWideSetup.resultStacks, SubexpNodeWideSetup.localResult,
        dimensionResult]
      omega
    simpa only [hb] using hm
  refine ⟨dimensionCost d + (n + m), Nat.add_le_add_left (Nat.add_le_add hn hm') _,
    out, hd.seq ((Eval.call SubexpNodeWideSetup.program ht).seq he), ?_⟩
  change Function.extend lowPorts f.stacks e.stacks = _
  rw [hfs, ProgramLinking.extend_update lowPorts_injective,
    ProgramLinking.extend_update lowPorts_injective]
  have hf := congrArg StructuredProgram.State.stacks
    (embedState_project id lowPorts e Function.injective_id lowPorts_injective)
  change Function.extend lowPorts (lowState e).stacks e.stacks = e.stacks at hf
  rw [hf]
  have h92 : Function.update e.stacks (92 : Fin 352)
      (List.replicate (SubexpSymbolicCost.indexBits D) true) = e.stacks := by
    apply Function.update_eq_self_iff.mpr
    simp [hs, SubexpNodeWideSetup.resultStacks, SubexpNodeWideSetup.localResult]
  change Function.update (Function.update e.stacks 92
    (List.replicate (SubexpSymbolicCost.indexBits D) true)) 25 _ = _
  rw [h92, hs]
  rfl

abbrev program : Program 16 352 (size command + 1) := compiled command 264 25

theorem program_runs (d : Data) (D : ℕ) (hr : Ready d)
    (hD : d.stacks 264 = List.replicate D true) :
    ∃ out : Data, RunsIn program (budget d D + 1)
      (d.withPC (some program.entry)) (out.withPC none) ∧ out.stacks = resultStacks d D := by
  obtain ⟨n, hn, out, he, hs⟩ := command_eval d D hr hD
  exact ⟨out, ⟨n + 1, by omega, compiled_halt_trace he 264 25⟩, hs⟩

end SubexponentialSAT.SubexpNodeWideInitialization

end OAI.Algorithms

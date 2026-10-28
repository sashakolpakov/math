import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeConstants
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Actual framing, index construction and storage of the zero/one raw literals. -/

namespace SubexponentialSAT.SubexpNodeRawConstants

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpArgumentEmitLoop

abbrev Data := State 16 256

def registers : Fin 5 → Fin 16 := Fin.castAdd 11
def ports (i : Fin 15) : Fin 256 := ⟨200 + i.val, by omega⟩
theorem registers_injective : Function.Injective registers := Fin.castAdd_injective _ _
theorem ports_injective : Function.Injective ports := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [ports] at hv
  omega

abbrev call : Cmd 16 256 :=
  .call (ProgramLinking.liftProgram SubexpScalarLiteralProgram.program registers ports)

def scalarInput (d : Data) (D : ℕ) (coefficient : List Bool) : State 5 15 :=
  ready (d.regs 0) (d.regs 1) (d.regs 2) (d.regs 3) (d.regs 4)
    (Encoding.frame coefficient) [false] D (SubexpSymbolicCost.indexBits D) 0 0 0 0 0

theorem call_eval (d : Data) (D : ℕ) (coefficient : List Bool)
    (hi : projectState registers ports d = scalarInput d D coefficient) :
    ∃ out : Data,
      Eval call (constantCost D (SubexpSymbolicCost.indexBits D) false coefficient + 1) d out ∧
      out.stacks = Function.update (Function.update d.stacks 200 []) 203
        (SubexpScalarLiteralProgram.rawLiteral D coefficient) := by
  let after := ready true false false false (d.regs 4) []
    (SubexpScalarLiteralProgram.rawLiteral D coefficient)
    D (SubexpSymbolicCost.indexBits D) 0 0 0 0 0
  have ht : Trace SubexpScalarLiteralProgram.program
      (constantCost D (SubexpSymbolicCost.indexBits D) false coefficient + 1)
      ((projectState registers ports d).withPC (some SubexpScalarLiteralProgram.program.entry))
      (after.withPC none) := by
    rw [hi]
    simpa only [scalarInput, List.append_nil] using
      SubexpScalarLiteralProgram.program_trace D coefficient []
        (d.regs 0) (d.regs 1) (d.regs 2) (d.regs 3) (d.regs 4)
  have hs : after.stacks = Function.update
      (Function.update (projectState registers ports d).stacks 0 []) 3
        (SubexpScalarLiteralProgram.rawLiteral D coefficient) := by
    rw [hi]
    funext i
    fin_cases i <;> simp [after, scalarInput, ready]
  refine ⟨embedState registers ports d after,
    eval_call_from_state _ _ _ _ registers_injective ports_injective ht, ?_⟩
  change Function.extend ports after.stacks d.stacks = _
  rw [hs, ProgramLinking.extend_update ports_injective,
    ProgramLinking.extend_update ports_injective]
  have he := congrArg StructuredProgram.State.stacks
    (embedState_project registers ports d registers_injective ports_injective)
  change Function.extend ports (projectState registers ports d).stacks d.stacks = d.stacks at he
  rw [he]
  rfl

def source (one : Bool) : Fin 256 := if one then 120 else 119
def destination (one : Bool) : Fin 256 := if one then 123 else 122

abbrev transfer (src dst : Fin 256) : Cmd 16 256 :=
  .call (StackRoutines.transferProgram src dst 0 1)

abbrev metadata : Cmd 16 256 := SubexpNodeCacheSetup.copies [(109, 207), (92, 208)]

abbrev initializeOutput : Cmd 16 256 :=
  .base (.seq (.atom (.set 0 false)) (.atom (.push 203 0)))

def outputInitialized (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks 203 (false :: d.stacks 203)⟩

theorem initializeOutput_eval (d : Data) :
    Eval initializeOutput 2 d (outputInitialized d) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 16) false) d).seq
    (StructuredProgram.Eval.atom (.push (203 : Fin 256) 0) _)
  exact .base (by simpa [outputInitialized, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h)

def prepared (one : Bool) (d : Data) : Data :=
  outputInitialized (SubexpNodeCacheSetup.copied [(109, 207), (92, 208)]
    (afterTransfer (SubexpNodeConstants.framed d (source one)) 215 200 0 1))

abbrev prepare (one : Bool) : Cmd 16 256 :=
  .seq (SubexpNodeConstants.frame (source one))
    (.seq (transfer 215 200) (.seq metadata initializeOutput))

def WorkEmpty (d : Data) : Prop :=
  ∀ i : Fin 256, 200 ≤ i.val → i.val ≤ 216 → d.stacks i = []

theorem frame_eval (d : Data) (one : Bool) (h216 : d.stacks 216 = []) :
    Eval (SubexpNodeConstants.frame (source one))
      (8 * (d.stacks (source one)).length + 7) d (SubexpNodeConstants.framed d (source one)) := by
  let mid : Data := ⟨Function.update d.regs 2 true, d.stacks⟩
  have hset : Eval (.base (.atom (.set 2 true))) 1 d mid :=
    .base (StructuredProgram.Eval.atom _ _)
  have hf := SubexpNodeConstants.frame_call_eval mid (source one)
    (by cases one <;> decide) (by cases one <;> decide) h216 (by simp [mid])
  have he : SubexpNodeConstants.framed mid (source one) =
      SubexpNodeConstants.framed d (source one) := by
    apply state_ext
    · funext i
      by_cases hi : i = 2 <;>
        simp [SubexpNodeConstants.framed, mid, Function.update_apply, hi]
    · rfl
  rw [he] at hf
  simpa only [SubexpNodeConstants.frame, mid,
    show ∀ n : ℕ, 1+(8*n+6)=8*n+7 by omega] using hset.seq hf

theorem prepare_eval (d : Data) (one : Bool) (h0 : d.stacks 0 = []) (hw : WorkEmpty d) :
    Eval (prepare one)
      (14 * (d.stacks (source one)).length +
        7 * ((d.stacks 109).length + (d.stacks 92).length) + 25)
      d (prepared one d) := by
  have hf := frame_eval d one (hw 216 (by decide) (by decide))
  let framed := SubexpNodeConstants.framed d (source one)
  let moved := afterTransfer framed 215 200 0 1
  have ht := transfer_eval framed 215 200 0 1 (by decide) (by decide)
  have hm := SubexpNodeCacheSetup.copies_eval [(109, 207), (92, 208)] moved
    (by simpa [moved, framed, afterTransfer, SubexpNodeConstants.framed,
      StackRoutines.transferStacks] using h0) (by
      intro m hm
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
      rcases hm with rfl | rfl <;> decide)
  have hi := initializeOutput_eval
    (SubexpNodeCacheSetup.copied [(109, 207), (92, 208)] moved)
  have he := hf.seq (ht.seq (hm.seq hi))
  convert he using 1
  all_goals simp [prepared, moved, framed,
      SubexpNodeConstants.framed, afterTransfer, StackRoutines.transferStacks,
      SubexpNodeCacheSetup.copyCost, afterCopy, StackRoutines.copyStacks,
      hw 215 (by decide) (by decide), Encoding.length_frame]
  all_goals omega

theorem prepared_stacks (d : Data) (one : Bool) (hw : WorkEmpty d) :
    (prepared one d).stacks = Function.update (Function.update
      (Function.update (Function.update d.stacks 200 (Encoding.frame (d.stacks (source one))))
        207 (d.stacks 109)) 208 (d.stacks 92)) 203 [false] := by
  have hreset : Function.update d.stacks (215 : Fin 256) [] = d.stacks :=
    Function.update_eq_self_iff.mpr (hw 215 (by decide) (by decide)).symm
  simp [prepared, outputInitialized, SubexpNodeCacheSetup.copied,
    afterCopy, StackRoutines.copyStacks, afterTransfer, StackRoutines.transferStacks,
    SubexpNodeConstants.framed, hw 200 (by decide) (by decide),
    hw 203 (by decide) (by decide), hw 207 (by decide) (by decide),
    hw 208 (by decide) (by decide), hw 215 (by decide) (by decide),
    List.reverse_reverse, hreset]

end SubexponentialSAT.SubexpNodeRawConstants

end OAI.Algorithms

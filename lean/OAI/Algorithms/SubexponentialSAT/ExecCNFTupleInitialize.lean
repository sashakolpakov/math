import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.TupleZeroProgram
import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleSplit
import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration

namespace OAI.Algorithms

/-!
# Actual mask-first tuple initialization in the candidate-search frame

The threshold on stack 15 and binary index width on stack 20 are preserved.
The real nested-counter tuple builder constructs index words on stack 17;
fixed code then prefixes the zero core mask. Only k occurs in this code's
finite control. Both the number and width of index words remain stack data.
-/

namespace SubexponentialSAT.ExecCNFTupleInitialize

open BitProgram StructuredCalls

abbrev Data := State 32 32
abbrev Code := Cmd 32 32

def zeroRegister (i : Fin 13) : Fin 32 := Fin.castAdd 19 i
def zeroStack : Fin 9 → Fin 32 := ![17, 22, 23, 19, 24, 25, 26, 27, 28]

theorem zeroRegister_injective : Function.Injective zeroRegister :=
  Fin.castAdd_injective 13 19

theorem zeroStack_injective : Function.Injective zeroStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [zeroStack]

def zeroCall : Code :=
  liftCommand TupleZeroProgram.command 1 0 zeroRegister zeroStack

def zeroReady (d : Data) : Prop :=
  d.stacks 17 = [] ∧ d.stacks 24 = [] ∧ d.stacks 25 = [] ∧
    d.stacks 26 = [] ∧ d.stacks 27 = [] ∧ d.stacks 28 = []

theorem zeroCall_eval (d : Data) (h : zeroReady d) :
    ∃ n e, Eval zeroCall n d e ∧
      n ≤ TupleZeroProgram.prependBound (d.stacks 22) (d.stacks 23) + 3 ∧
      e.stacks 17 = TupleZeroProgram.output (d.stacks 22) (d.stacks 23) ∧
      e.stacks 22 = [] ∧ e.stacks 23 = [] ∧
      (∀ i : Fin 32, i ≠ 17 → i ≠ 22 → i ≠ 23 → e.stacks i = d.stacks i) := by
  rcases h with ⟨h17, h24, h25, h26, h27, h28⟩
  obtain ⟨n, regs, he, hn⟩ := TupleZeroProgram.command_eval
    (d.regs ∘ zeroRegister) (d.stacks 22) (d.stacks 23) (d.stacks 19)
  have hp : projectState zeroRegister zeroStack d =
      TupleZeroProgram.initialState (d.regs ∘ zeroRegister)
        (d.stacks 22) (d.stacks 23) (d.stacks 19) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [ zeroStack,
        h17, h24, h25, h26, h27, h28]
  let localResult := TupleZeroProgram.finalState regs
    (TupleZeroProgram.output (d.stacks 22) (d.stacks 23)) (d.stacks 19)
  let e := embedState zeroRegister zeroStack d localResult
  have heval : Eval zeroCall (n + 1) d e :=
    eval_liftCommand_from_state _ 1 0 zeroRegister zeroStack d
      zeroRegister_injective zeroStack_injective (by simpa only [hp] using he)
  have hport (j : Fin 9) : e.stacks (zeroStack j) = localResult.stacks j :=
    embedState_stack _ _ _ _ zeroStack_injective j
  refine ⟨n + 1, e, heval, by omega, hport 0, hport 1, hport 2, ?_⟩
  intro i hi17 hi22 hi23
  by_cases hi : ∃ j, zeroStack j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [hport]
    fin_cases j <;> simp_all [zeroStack, localResult, TupleZeroProgram.finalState]
  · exact embedState_stack_frame _ _ _ _ i hi

def push (bit : Bool) : Code :=
  .base (.seq (.atom (.set 0 bit)) (.atom (.push 17 0)))

abbrev pushed (bit : Bool) (d : Data) : Data :=
  ⟨Function.update d.regs 0 bit, Function.update d.stacks 17 (bit :: d.stacks 17)⟩

theorem push_eval (bit : Bool) (d : Data) : Eval (push bit) 2 d (pushed bit d) := by
  apply Eval.base
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 32) bit) d).seq
    (StructuredProgram.Eval.atom (.push (17 : Fin 32) 0) _)
  simpa [push, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

/-- The word here is fixed at compilation, never a runtime dimension. -/
def prependBits : List Bool → Code
  | [] => .base .skip
  | bit :: rest => .seq (prependBits rest) (push bit)

def prefixed : List Bool → Data → Data
  | [], d => d
  | bit :: rest, d => pushed bit (prefixed rest d)

theorem prependBits_eval (bits : List Bool) (d : Data) :
    Eval (prependBits bits) (2 * bits.length) d (prefixed bits d) := by
  induction bits with
  | nil => exact .base (.skip _)
  | cons bit rest ih =>
    simpa only [prependBits, prefixed, List.length_cons, Nat.mul_add, Nat.mul_one]
      using Eval.seq ih (push_eval bit (prefixed rest d))

theorem prefixed_stacks (bits : List Bool) (d : Data) :
    (prefixed bits d).stacks = Function.update d.stacks 17 (bits ++ d.stacks 17) := by
  induction bits with
  | nil => simp [prefixed]
  | cons bit rest ih =>
    simp [prefixed, pushed, ih, List.cons_append, Function.update_idem]

theorem prependBits_size (bits : List Bool) : size (prependBits bits) = 2 * bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp [prependBits, push, size, StructuredProgram.size, ih, Nat.mul_add]

def maskPrefix (k : ℕ) : List Bool := true :: Encoding.frame (List.replicate k false)

theorem maskPrefix_length (k : ℕ) : (maskPrefix k).length = 2 * k + 2 := by
  simp [maskPrefix, Encoding.length_frame]

def command (k : ℕ) : Code :=
  .seq (ExecCNFTupleSplit.copy 15 22)
    (.seq (ExecCNFTupleSplit.copy 20 23) (.seq zeroCall (prependBits (maskPrefix k))))

def program (k : ℕ) := compiled (command k) 15 17

def Ready (d : Data) : Prop :=
  zeroReady d ∧ d.stacks 22 = [] ∧ d.stacks 23 = []

def words (k : ℕ) (rows width : List Bool) : List (List Bool) :=
  List.replicate k false ::
    List.replicate (CounterPrograms.value rows) (List.replicate (CounterPrograms.value width) false)

def bound (k : ℕ) (rows width : List Bool) : ℕ :=
  7 * rows.length + 7 * width.length + TupleZeroProgram.prependBound rows width + 4 * k + 17

/-- Actual per-width preparation, with threshold/width/formula/bank/witness
unchanged and every temporary stack available again to the callback. -/
theorem command_eval (k : ℕ) (d : Data) (h : Ready d) :
    ∃ n e, Eval (command k) n d e ∧ n ≤ bound k (d.stacks 15) (d.stacks 20) ∧
      e.stacks 17 = Encoding.encodeList id (words k (d.stacks 15) (d.stacks 20)) ∧
      (∀ i : Fin 32, i ≠ 17 → e.stacks i = d.stacks i) := by
  rcases h with ⟨hz, h22, h23⟩
  have h25 : d.stacks 25 = [] := hz.2.2.1
  let a := ExecCNFTupleSplit.copied 15 22 d
  let b := ExecCNFTupleSplit.copied 20 23 a
  have ha25 : a.stacks 25 = [] :=
    (ExecCNFTupleSplit.copied_stack_frame 15 22 d 25 (by decide)).trans h25
  have ha20 : a.stacks 20 = d.stacks 20 :=
    ExecCNFTupleSplit.copied_stack_frame 15 22 d 20 (by decide)
  have hb22 : b.stacks 22 = d.stacks 15 := by
    simp [b, a, ExecCNFTupleSplit.copied, StackRoutines.copyStacks, h22]
  have hb23 : b.stacks 23 = d.stacks 20 := by
    simp [b, a, ExecCNFTupleSplit.copied, StackRoutines.copyStacks, h23]
  have hbframe (i : Fin 32) (h22 : i ≠ 22) (h23 : i ≠ 23) : b.stacks i = d.stacks i :=
    (ExecCNFTupleSplit.copied_stack_frame 20 23 a i h23).trans
      (ExecCNFTupleSplit.copied_stack_frame 15 22 d i h22)
  have hbz : zeroReady b := by
    rcases hz with ⟨h17, h24, h25, h26, h27, h28⟩
    exact ⟨(hbframe 17 (by decide) (by decide)).trans h17,
      (hbframe 24 (by decide) (by decide)).trans h24,
      (hbframe 25 (by decide) (by decide)).trans h25,
      (hbframe 26 (by decide) (by decide)).trans h26,
      (hbframe 27 (by decide) (by decide)).trans h27,
      (hbframe 28 (by decide) (by decide)).trans h28⟩
  obtain ⟨n, e, he, hn, he17, he22, he23, hef⟩ := zeroCall_eval b hbz
  refine ⟨(7 * (d.stacks 15).length + 5) +
      ((7 * (a.stacks 20).length + 5) + (n + 2 * (maskPrefix k).length)),
    prefixed (maskPrefix k) e, ?_, ?_, ?_, ?_⟩
  · exact Eval.seq (ExecCNFTupleSplit.copy_eval 15 22 d (by decide) (by decide) (by decide) h25)
      (Eval.seq (ExecCNFTupleSplit.copy_eval 20 23 a (by decide) (by decide) (by decide) ha25)
        (Eval.seq he (prependBits_eval (maskPrefix k) e)))
  · rw [hb22, hb23] at hn
    rw [ha20, maskPrefix_length]
    unfold bound
    omega
  · rw [prefixed_stacks, Function.update_self, he17, hb22, hb23]
    rfl
  · intro i hi
    rw [prefixed_stacks, Function.update_of_ne hi]
    by_cases hi22 : i = 22
    · subst i; exact he22.trans h22.symm
    by_cases hi23 : i = 23
    · subst i; exact he23.trans h23.symm
    exact (hef i hi hi22 hi23).trans (hbframe i hi22 hi23)

theorem words_shape (k : ℕ) (rows width : List Bool) :
    (words k rows width).map List.length =
      [k] ++ List.replicate (CounterPrograms.value rows) (CounterPrograms.value width) := by
  simp [words]

theorem words_value (k : ℕ) (rows width : List Bool) :
    CounterPrograms.value (words k rows width).flatten = 0 := by
  simp [words, List.flatten_replicate_replicate,
    ExecCNFTupleEnumeration.value_replicate_false]

theorem encoded_length (k : ℕ) (rows width : List Bool) :
    (Encoding.encodeList id (words k rows width)).length =
      2 * (k + CounterPrograms.value rows * CounterPrograms.value width) +
        2 * (CounterPrograms.value rows + 1) + 1 := by
  rw [ExecCNFTupleOdometer.encoded_length]
  simp [words, List.flatten_replicate_replicate, Nat.add_comm]

/-- Only the fixed core-mask size contributes variable code size. -/
theorem command_size (k : ℕ) : size (command k) = 4 * k + 116 := by
  rw [command]
  simp only [size, ExecCNFTupleSplit.copy, zeroCall, liftCommand]
  rw [TupleZeroProgram.command_size, prependBits_size, maskPrefix_length]
  omega

theorem program_runs (k : ℕ) (d : Data) (h : Ready d) :
    ∃ e : Data, RunsIn (program k) (bound k (d.stacks 15) (d.stacks 20) + 1)
      (d.withPC (some (program k).entry)) (e.withPC none) ∧
      e.stacks 17 = Encoding.encodeList id (words k (d.stacks 15) (d.stacks 20)) ∧
      (∀ i : Fin 32, i ≠ 17 → e.stacks i = d.stacks i) := by
  obtain ⟨n, e, he, hn, ht, hf⟩ := command_eval k d h
  exact ⟨e, ⟨n + 1, by omega, compiled_halt_trace he 15 17⟩, ht, hf⟩

theorem program_primitive (k : ℕ) (d : Data) (h : Ready d) :
    ∃ e : Data, Computation.RunsIn (primitive (program k)).step
      (primitiveOverhead (program k) * (bound k (d.stacks 15) (d.stacks 20) + 1))
      (primitiveCfg (program k) (d.withPC (some (program k).entry)))
      (primitiveCfg (program k) (e.withPC none)) ∧
      e.stacks 17 = Encoding.encodeList id (words k (d.stacks 15) (d.stacks 20)) ∧
      (∀ i : Fin 32, i ≠ 17 → e.stacks i = d.stacks i) := by
  obtain ⟨e, he, ht, hf⟩ := program_runs k d h
  exact ⟨e, BitProgram.primitive_execution (program k) he, ht, hf⟩

end SubexponentialSAT.ExecCNFTupleInitialize

end OAI.Algorithms

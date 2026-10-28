import OAI.Algorithms.SubexponentialSAT.CounterForPrograms
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CountModel
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace

/-! Canonical unsigned binary output by a fixed finite word program.
The program reverses its input, removes high zeroes, reverses back, and emits
one false bit in the empty case. All source stack prefixes have a linear local
bound. No algebraic construction is imported to implement normalization. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram

open BitProgram StructuredCalls CounterPrograms

abbrev Data := StructuredProgram.State 3 3

def zeroRegs : Fin 3 → Bool := fun _ => false

def state (regs : Fin 3 → Bool) (input output : List Bool) : Data :=
  ⟨regs, ![input, output, []]⟩

def dropZeroes : List Bool → List Bool
  | [] => []
  | false :: xs => dropZeroes xs
  | true :: xs => true :: xs

def nonemptyWord (xs : List Bool) : List Bool := if xs = [] then [false] else xs

def normalized (xs : List Bool) : List Bool := nonemptyWord (dropZeroes xs.reverse).reverse

theorem dropZeroes_length (xs : List Bool) : (dropZeroes xs).length ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [dropZeroes]; omega

theorem value_append (xs ys : List Bool) :
    value (xs ++ ys) = value xs + 2 ^ xs.length * value ys := by
  induction xs with
  | nil => simp
  | cons b xs ih => simp [value, ih, Nat.pow_succ, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.add_assoc]

theorem ofDigits_eq_value (word : List Bool) :
    Nat.ofDigits 2 (word.map Bool.toNat) = value word := by
  induction word with
  | nil => rfl
  | cons b word ih => simp only [List.map_cons, Nat.ofDigits_cons, value, ih]

theorem normalized_eq_binaryNat (word : List Bool) :
    normalized word = binaryNat (value word) := by
  induction word using List.reverseRecOn with
  | nil => simp [normalized, dropZeroes, nonemptyWord, binaryNat_zero]
  | append_singleton word b ih =>
    cases b with
    | false => simpa [normalized, List.reverse_append, dropZeroes, value_append, value] using ih
    | true =>
      apply eq_binaryNat_of_decode
      · have hn : normalized (word ++ [true]) = word ++ [true] := by
          simp [normalized, List.reverse_append, dropZeroes, nonemptyWord]
        rw [hn]
        exact ofDigits_eq_value _
      · right
        exact ⟨word, by simp [normalized, List.reverse_append, dropZeroes, nonemptyWord]⟩

def reset : Cmd 3 3 := .base
  (.seq (.atom (.set 0 false)) (.seq (.atom (.set 1 false)) (.atom (.set 2 false))))

theorem reset_eval (regs : Fin 3 → Bool) (word : List Bool) :
    Eval reset 3 (state regs word []) (state zeroRegs word []) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) false) (state regs word [])).seq
    ((StructuredProgram.Eval.atom (.set (1 : Fin 3) false) _).seq
      (StructuredProgram.Eval.atom (.set (2 : Fin 3) false) _))
  apply Eval.base
  convert h using 1
  apply CounterForPrograms.data_ext
  · funext i
    fin_cases i <;> simp [state, zeroRegs, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  · rfl

def test : Cmd 3 3 := .base
  (.seq (.atom (.peek 1 0 1))
    (.seq (.atom (.bnot 2 0)) (.atom (.band 2 2 1))))

def tested (xs : List Bool) : Data :=
  state (counterRegs (xs.headD false) (!xs.isEmpty) ((!xs.headD false) && !xs.isEmpty)) [] xs

theorem test_eval (regs : Fin 3 → Bool) (xs : List Bool) :
    Eval test 3 (state regs [] xs) (tested xs) := by
  have h := (StructuredProgram.Eval.atom (.peek (1 : Fin 3) (0 : Fin 3) (1 : Fin 3))
    (state regs [] xs)).seq
    ((StructuredProgram.Eval.atom (.bnot (2 : Fin 3) (0 : Fin 3)) _).seq
      (StructuredProgram.Eval.atom (.band (2 : Fin 3) (2 : Fin 3) (1 : Fin 3)) _))
  apply Eval.base
  convert h using 1
  apply CounterForPrograms.data_ext
  · funext i
    cases xs with
    | nil => fin_cases i <;> simp [tested, state, counterRegs, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
    | cons b xs => cases b <;> fin_cases i <;>
        simp [tested, state, counterRegs, StructuredProgram.Atom.eval,
          StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
  · rfl

def dropBody : Cmd 3 3 := .seq (.base (.atom (.pop 1 0 1))) test

def dropLoop : Cmd 3 3 := .while 2 dropBody

theorem dropBody_eval (xs : List Bool) :
    Eval dropBody 4 (tested (false :: xs)) (tested xs) := by
  have h := StructuredProgram.Eval.atom (.pop (1 : Fin 3) (0 : Fin 3) (1 : Fin 3))
    (tested (false :: xs))
  have he : (StructuredProgram.Atom.pop (1 : Fin 3) 0 1).eval (tested (false :: xs)) =
      state (counterRegs false true true) [] xs := by
    apply CounterForPrograms.data_ext
    · funext i
      fin_cases i <;> simp [tested, state, counterRegs, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
    · funext i
      fin_cases i <;> simp [tested, state, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  rw [he] at h
  exact (Eval.base h).seq (test_eval _ xs)

theorem dropLoop_eval (xs : List Bool) :
    ∃ n, n ≤ 5 * xs.length + 1 ∧ Eval dropLoop n (tested xs) (tested (dropZeroes xs)) := by
  induction xs with
  | nil => exact ⟨1, by simp, Eval.while_false rfl⟩
  | cons b xs ih =>
    cases b with
    | true => exact ⟨1, by simp, Eval.while_false rfl⟩
    | false =>
      obtain ⟨n, hn, he⟩ := ih
      exact ⟨4 + n + 1, by simp only [List.length_cons]; omega,
        Eval.while_true rfl (dropBody_eval xs) he⟩

def transferred (d : Data) (src dst : Fin 3) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

theorem transfer_eval (d : Data) (src dst : Fin 3) (h : src ≠ dst) :
    Eval (.call (StackRoutines.transferProgram src dst 0 1))
      (3 * (d.stacks src).length + 3) d (transferred d src dst) :=
  Eval.call _ (ListRegisterProgram.transfer_run src dst 0 1 h (by decide) d.regs d.stacks)

def emitZero : Cmd 3 3 := .seq
  (.base (.seq (.atom (.set 0 false)) (.atom (.push 0 0)))) reset

theorem emitZero_eval (regs : Fin 3 → Bool) :
    Eval emitZero 5 (state regs [] []) (state zeroRegs [false] []) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) false) (state regs [] [])).seq
    (StructuredProgram.Eval.atom (.push (0 : Fin 3) (0 : Fin 3)) _)
  have he : (StructuredProgram.Atom.push (0 : Fin 3) 0).eval
      ((StructuredProgram.Atom.set (0 : Fin 3) false).eval (state regs [] [])) =
      state (Function.update regs 0 false) [false] [] := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      fin_cases i <;> simp [state, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  rw [he] at h
  exact (Eval.base h).seq (reset_eval _ _)

def finish : Cmd 3 3 := .seq (.base (.atom (.peek 0 0 1))) (.ite 1 reset emitZero)

theorem finish_eval (regs : Fin 3 → Bool) (xs : List Bool) :
    ∃ n, n ≤ 7 ∧ Eval finish n (state regs xs []) (state zeroRegs (nonemptyWord xs) []) := by
  have h := StructuredProgram.Eval.atom (.peek (0 : Fin 3) (0 : Fin 3) (1 : Fin 3))
    (state regs xs [])
  have he : (StructuredProgram.Atom.peek (0 : Fin 3) 0 1).eval (state regs xs []) =
      state (readRegs regs 0 1 xs.head?) xs [] := rfl
  rw [he] at h
  cases xs with
  | nil => exact ⟨7, by decide, (Eval.base h).seq (Eval.ite_false (by simp [state, readRegs])
      (emitZero_eval _))⟩
  | cons b xs => exact ⟨5, by decide, (Eval.base h).seq
      (Eval.ite_true (by simp [state, readRegs]) (reset_eval _ _))⟩

/-- A single fixed finite control table, independent of input length/value. -/
def normalizeUnsigned : Cmd 3 3 :=
  .seq (.call (StackRoutines.transferProgram 0 1 0 1))
    (.seq test (.seq dropLoop (.seq (.call (StackRoutines.transferProgram 1 0 0 1)) finish)))

theorem normalizeUnsigned_eval (regs : Fin 3 → Bool) (word : List Bool) :
    ∃ n, n ≤ 17 * word.length + 28 ∧ Eval normalizeUnsigned n
      (state regs word []) (state zeroRegs (binaryNat (value word)) []) := by
  let first := readRegs regs 0 1 none
  have hfirst : transferred (state regs word []) 0 1 = state first [] word.reverse := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      fin_cases i <;> simp [transferred, state, StackRoutines.transferStacks]
  have h1 := transfer_eval (state regs word []) 0 1 (by decide)
  rw [hfirst] at h1
  have h2 := test_eval first word.reverse
  obtain ⟨n, hn, h3⟩ := dropLoop_eval word.reverse
  have h4 := transfer_eval (tested (dropZeroes word.reverse)) 1 0 (by decide)
  let lastRegs := readRegs (tested (dropZeroes word.reverse)).regs 0 1 none
  have hlast : transferred (tested (dropZeroes word.reverse)) 1 0 =
      state lastRegs (dropZeroes word.reverse).reverse [] := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      fin_cases i <;> simp [transferred, tested, state, StackRoutines.transferStacks]
  rw [hlast] at h4
  obtain ⟨m, hm, h5⟩ := finish_eval lastRegs (dropZeroes word.reverse).reverse
  have hout : nonemptyWord (dropZeroes word.reverse).reverse = binaryNat (value word) :=
    normalized_eq_binaryNat word
  rw [hout] at h5
  refine ⟨(3 * word.length + 3) + (3 + (n +
      ((3 * (dropZeroes word.reverse).length + 3) + m))), ?_, ?_⟩
  · have hl := dropZeroes_length word.reverse
    simp only [List.length_reverse] at hn hl
    omega
  · exact h1.seq (h2.seq (h3.seq (h4.seq h5)))

def normalizeUnsignedProgram : Program 3 3 (StructuredCalls.size normalizeUnsigned + 1) :=
  StructuredCalls.compiled normalizeUnsigned 0 0

theorem normalizeUnsigned_runs (word : List Bool) :
    RunsIn normalizeUnsignedProgram (17 * word.length + 29)
      (initial normalizeUnsignedProgram word)
      (terminal normalizeUnsignedProgram (binaryNat (value word))) := by
  obtain ⟨n, hn, he⟩ := normalizeUnsigned_eval zeroRegs word
  refine ⟨n + 1, by omega, ?_⟩
  have ha : initial normalizeUnsignedProgram word =
      (state zeroRegs word []).withPC
        (some normalizeUnsignedProgram.entry) := by
    apply congrArg (fun tapeWords =>
      Cfg.mk (some normalizeUnsignedProgram.entry) zeroRegs tapeWords)
    funext j
    fin_cases j <;> rfl
  have hb : terminal normalizeUnsignedProgram (binaryNat (value word)) =
      (state zeroRegs
        (binaryNat (value word)) []).withPC none := by
    apply congrArg (fun tapeWords => Cfg.mk none zeroRegs tapeWords)
    funext j
    fin_cases j <;> rfl
  rw [ha, hb]
  exact StructuredCalls.compiled_halt_trace he 0 0

theorem normalizeUnsigned_call {R S : ℕ}
    (register : Fin 3 ↪ Fin R) (stack : Fin 3 ↪ Fin S)
    (frame : State R S) (regs : Fin 3 → Bool) (word : List Bool) :
    ∃ n, n ≤ 17 * word.length + 29 ∧
      Eval (.call (ProgramLinking.liftProgram normalizeUnsignedProgram register stack)) n
        (embedState register stack frame (state regs word []))
        (embedState register stack frame
          (state zeroRegs
            (binaryNat (value word)) [])) := by
  obtain ⟨n, hn, he⟩ := normalizeUnsigned_eval regs word
  exact ⟨n + 1, by omega,
    eval_call_lifted normalizeUnsignedProgram register stack frame
      register.injective stack.injective (StructuredCalls.compiled_halt_trace he 0 0)⟩

/-- All stacks of the normalization subroutine are bounded at every source
instruction. Its own linear runtime is used only for this local routine. -/
theorem normalizeUnsigned_prefix_space (word : List Bool) (prefixSteps : ℕ)
    (c : Cfg 3 3 (StructuredCalls.size normalizeUnsigned + 1))
    (hp : prefixSteps ≤ 17 * word.length + 29)
    (htrace : Trace normalizeUnsignedProgram prefixSteps
      (initial normalizeUnsignedProgram word) c) :
    dataBits c ≤ 18 * word.length + 29 := by
  have h := trace_dataBits normalizeUnsignedProgram htrace
  rw [initial_dataBits] at h
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BitProgram
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile
import OAI.Algorithms.SubexponentialSAT.Encoding
import OAI.Algorithms.SubexponentialSAT.ProgramLinking
import OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace OAI.Algorithms

/-!
# Fixed-control parsers for the canonical formula encoding

These programs operate on two Boolean stacks and two Boolean registers.
Stack 0 is input; stack 1 accumulates output. Register 0 holds the last data
bit and register 1 records whether the last pop succeeded. Thus register 1
is true on successful delimiter termination and false on malformed input.
All stated running times count actual `BitProgram.step` transitions.
-/

namespace SubexponentialSAT.ParserProgram

open SubexponentialSAT.BitProgram

def pair {α : Type*} (a b : α) : Fin 2 → α := fun i => if i = 0 then a else b

@[simp] theorem pair_zero {α : Type*} (a b : α) : pair a b 0 = a := rfl
@[simp] theorem pair_one {α : Type*} (a b : α) : pair a b 1 = b := rfl

@[simp] theorem update_pair_zero {α : Type*} (a b c : α) :
    Function.update (pair a b) 0 c = pair c b := by
  funext i
  fin_cases i <;> simp [pair]

@[simp] theorem update_pair_one {α : Type*} (a b c : α) :
    Function.update (pair a b) 1 c = pair a c := by
  funext i
  fin_cases i <;> simp [pair]

def cfg {l : ℕ} (pc : Option (Fin l)) (value present : Bool)
    (input output : List Bool) : Cfg 2 2 l :=
  ⟨pc, pair value present, pair input output⟩

/-- Five fixed labels suffice to decode an arbitrary unary natural field. -/
abbrev natProgram : Program 2 2 5 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .branch 1 2 4
    | 2 => .branch 0 3 4
    | 3 => .push 1 0 0
    | _ => .halt

theorem nat_pop (b v p : Bool) (input output : List Bool) :
    step natProgram (cfg (some 0) v p (b :: input) output) =
      some (cfg (some 1) b true input output) := by
  simp [step, cfg, execInstr, readRegs]

theorem nat_present (v : Bool) (input output : List Bool) :
    step natProgram (cfg (some 1) v true input output) =
      some (cfg (some 2) v true input output) := by
  simp [step, cfg, execInstr]

theorem nat_true (input output : List Bool) :
    step natProgram (cfg (some 2) true true input output) =
      some (cfg (some 3) true true input output) := by
  simp [step, cfg, execInstr]

theorem nat_push (input output : List Bool) :
    step natProgram (cfg (some 3) true true input output) =
      some (cfg (some 0) true true input (true :: output)) := by
  simp [step, cfg, execInstr]

theorem nat_false (input output : List Bool) :
    step natProgram (cfg (some 2) false true input output) =
      some (cfg (some 4) false true input output) := by
  simp [step, cfg, execInstr]

theorem nat_halt (v p : Bool) (input output : List Bool) :
    step natProgram (cfg (some 4) v p input output) =
      some (cfg none v p input output) := by
  simp [step, cfg, execInstr]

theorem nat_cycle (v p : Bool) (input output : List Bool) :
    Trace natProgram 4 (cfg (some 0) v p (true :: input) output)
      (cfg (some 0) true true input (true :: output)) :=
  .cons (nat_pop true v p input output)
    (.cons (nat_present true input output)
      (.cons (nat_true input output) (.cons (nat_push input output) (.refl _))))

theorem nat_finish (v p : Bool) (input output : List Bool) :
    Trace natProgram 4 (cfg (some 0) v p (false :: input) output)
      (cfg none false true input output) :=
  .cons (nat_pop false v p input output)
    (.cons (nat_present false input output)
      (.cons (nat_false input output) (.cons (nat_halt false true input output) (.refl _))))

/-- The count is data on stack 1, rather than an input-dependent control state. -/
theorem nat_trace (n : ℕ) (rest output : List Bool) (v p : Bool) :
    Trace natProgram (4 * n + 4)
      (cfg (some 0) v p (Encoding.encodeNat n ++ rest) output)
      (cfg none false true rest (List.replicate n true ++ output)) := by
  induction n generalizing output v p with
  | zero => simpa [Encoding.encodeNat] using nat_finish v p rest output
  | succ n ih =>
      have h := (nat_cycle v p (Encoding.encodeNat n ++ rest) output).trans
        (ih (true :: output) true true)
      have ht : 4 + (4 * n + 4) = 4 * (n + 1) + 4 := by omega
      have hin : Encoding.encodeNat (n + 1) ++ rest =
          true :: (Encoding.encodeNat n ++ rest) := by
        simp [Encoding.encodeNat, List.replicate_succ]
      simpa only [ht, hin, List.replicate_succ', List.append_assoc,
        List.singleton_append] using h

theorem nat_runsIn (n : ℕ) (rest output : List Bool) (v p : Bool) :
    RunsIn natProgram (4 * n + 4)
      (cfg (some 0) v p (Encoding.encodeNat n ++ rest) output)
      (cfg none false true rest (List.replicate n true ++ output)) :=
  ⟨_, le_rfl, nat_trace n rest output v p⟩

/-- An incomplete natural field is detected, rather than accepted as zero. -/
theorem nat_empty_reject (output : List Bool) (v p : Bool) :
    Trace natProgram 3 (cfg (some 0) v p [] output)
      (cfg none false false [] output) := by
  have hpop : step natProgram (cfg (some 0) v p [] output) =
      some (cfg (some 1) false false [] output) := by
    simp [step, cfg, execInstr, readRegs]
  have hbranch : step natProgram (cfg (some 1) false false [] output) =
      some (cfg (some 4) false false [] output) := by
    simp [step, cfg, execInstr]
  exact .cons hpop (.cons hbranch (.cons (nat_halt false false [] output) (.refl _)))

/-- Seven fixed labels read escaped frames of arbitrary length. The payload
is reversed on the destination stack; a stack-transfer routine restores order. -/
abbrev frameProgram : Program 2 2 7 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .branch 1 2 6
    | 2 => .branch 0 3 6
    | 3 => .pop 0 0 1 4
    | 4 => .branch 1 5 6
    | 5 => .push 1 0 0
    | _ => .halt

theorem frame_pop_tag (b v p : Bool) (input output : List Bool) :
    step frameProgram (cfg (some 0) v p (b :: input) output) =
      some (cfg (some 1) b true input output) := by
  simp [step, cfg, execInstr, readRegs]

theorem frame_present_tag (v : Bool) (input output : List Bool) :
    step frameProgram (cfg (some 1) v true input output) =
      some (cfg (some 2) v true input output) := by
  simp [step, cfg, execInstr]

theorem frame_true_tag (input output : List Bool) :
    step frameProgram (cfg (some 2) true true input output) =
      some (cfg (some 3) true true input output) := by
  simp [step, cfg, execInstr]

theorem frame_pop_data (b v p : Bool) (input output : List Bool) :
    step frameProgram (cfg (some 3) v p (b :: input) output) =
      some (cfg (some 4) b true input output) := by
  simp [step, cfg, execInstr, readRegs]

theorem frame_present_data (v : Bool) (input output : List Bool) :
    step frameProgram (cfg (some 4) v true input output) =
      some (cfg (some 5) v true input output) := by
  simp [step, cfg, execInstr]

theorem frame_push (b : Bool) (input output : List Bool) :
    step frameProgram (cfg (some 5) b true input output) =
      some (cfg (some 0) b true input (b :: output)) := by
  simp [step, cfg, execInstr]

theorem frame_false_tag (input output : List Bool) :
    step frameProgram (cfg (some 2) false true input output) =
      some (cfg (some 6) false true input output) := by
  simp [step, cfg, execInstr]

theorem frame_halt (v p : Bool) (input output : List Bool) :
    step frameProgram (cfg (some 6) v p input output) =
      some (cfg none v p input output) := by
  simp [step, cfg, execInstr]

theorem frame_cycle (b v p : Bool) (input output : List Bool) :
    Trace frameProgram 6 (cfg (some 0) v p (true :: b :: input) output)
      (cfg (some 0) b true input (b :: output)) :=
  .cons (frame_pop_tag true v p (b :: input) output)
    (.cons (frame_present_tag true (b :: input) output)
      (.cons (frame_true_tag (b :: input) output)
        (.cons (frame_pop_data b true true input output)
          (.cons (frame_present_data b input output)
            (.cons (frame_push b input output) (.refl _))))))

theorem frame_finish (v p : Bool) (input output : List Bool) :
    Trace frameProgram 4 (cfg (some 0) v p (false :: input) output)
      (cfg none false true input output) :=
  .cons (frame_pop_tag false v p input output)
    (.cons (frame_present_tag false input output)
      (.cons (frame_false_tag input output)
        (.cons (frame_halt false true input output) (.refl _))))

/-- Exact measured execution of the actual parser, preserving the unused suffix. -/
theorem frame_trace (bits rest output : List Bool) (v p : Bool) :
    Trace frameProgram (6 * bits.length + 4)
      (cfg (some 0) v p (Encoding.frame bits ++ rest) output)
      (cfg none false true rest (bits.reverse ++ output)) := by
  induction bits generalizing output v p with
  | nil => simpa [Encoding.frame_nil] using frame_finish v p rest output
  | cons b bits ih =>
      have h := (frame_cycle b v p (Encoding.frame bits ++ rest) output).trans
        (ih (b :: output) b true)
      have ht : 6 + (6 * bits.length + 4) = 6 * (b :: bits).length + 4 := by
        simp only [List.length_cons]
        omega
      simpa only [ht, Encoding.frame_cons, List.cons_append, List.reverse_cons,
        List.append_assoc, List.singleton_append, List.nil_append] using h

theorem frame_runsIn (bits rest output : List Bool) (v p : Bool) :
    RunsIn frameProgram (6 * bits.length + 4)
      (cfg (some 0) v p (Encoding.frame bits ++ rest) output)
      (cfg none false true rest (bits.reverse ++ output)) :=
  ⟨_, le_rfl, frame_trace bits rest output v p⟩

theorem frame_empty_reject (output : List Bool) (v p : Bool) :
    Trace frameProgram 3 (cfg (some 0) v p [] output)
      (cfg none false false [] output) := by
  have hpop : step frameProgram (cfg (some 0) v p [] output) =
      some (cfg (some 1) false false [] output) := by
    simp [step, cfg, execInstr, readRegs]
  have hbranch : step frameProgram (cfg (some 1) false false [] output) =
      some (cfg (some 6) false false [] output) := by
    simp [step, cfg, execInstr]
  exact .cons hpop (.cons hbranch (.cons (frame_halt false false [] output) (.refl _)))

theorem frame_missing_data_reject (output : List Bool) (v p : Bool) :
    Trace frameProgram 6 (cfg (some 0) v p [true] output)
      (cfg none false false [] output) := by
  have hpop : step frameProgram (cfg (some 3) true true [] output) =
      some (cfg (some 4) false false [] output) := by
    simp [step, cfg, execInstr, readRegs]
  have hbranch : step frameProgram (cfg (some 4) false false [] output) =
      some (cfg (some 6) false false [] output) := by
    simp [step, cfg, execInstr]
  exact .cons (frame_pop_tag true v p [] output)
    (.cons (frame_present_tag true [] output)
      (.cons (frame_true_tag [] output) (.cons hpop (.cons hbranch
        (.cons (frame_halt false false [] output) (.refl _))))))

/-- The formula's declared coordinate count is parsed by the same fixed program. -/
theorem formula_header_trace {n : ℕ} (F : SAT.CNF (Fin n)) (v p : Bool) :
    Trace natProgram (4 * n + 4)
      (cfg (some 0) v p (Encoding.encodeCNF F) [])
      (cfg none false true (Encoding.encodeCNFBody F) (List.replicate n true)) := by
  simpa [Encoding.encodeCNF] using nat_trace n (Encoding.encodeCNFBody F) [] v p

theorem formula_header_runsIn_length {n : ℕ} (F : SAT.CNF (Fin n)) (v p : Bool) :
    RunsIn natProgram (4 * Encoding.formulaBitLength F + 4)
      (cfg (some 0) v p (Encoding.encodeCNF F) [])
      (cfg none false true (Encoding.encodeCNFBody F) (List.replicate n true)) := by
  refine ⟨4 * n + 4, ?_, formula_header_trace F v p⟩
  have := Encoding.numVariables_le_formulaBitLength F
  omega

/-- Frame parsing agrees with the project's pure decoder; this pairs the
syntax equality with an actual bounded execution certificate. -/
theorem frame_decoding_agreement (bits rest : List Bool) :
    Encoding.readFrame (Encoding.frame bits ++ rest) = some (bits, rest) ∧
    Trace frameProgram (6 * bits.length + 4)
      (cfg (some 0) false false (Encoding.frame bits ++ rest) [])
      (cfg none false true rest bits.reverse) := by
  refine ⟨Encoding.readFrame_frame_append bits rest, ?_⟩
  simpa using frame_trace bits rest [] false false

/-- A successful pure natural-field parse characterizes the consumed prefix. -/
theorem nat_input_shape : (input : List Bool) → (n : ℕ) → (rest : List Bool) →
    Encoding.readNat input = some (n, rest) → input = Encoding.encodeNat n ++ rest
  | [], n, rest, h => by simp [Encoding.readNat] at h
  | false :: input, n, rest, h => by
      have hp : (0, input) = (n, rest) := Option.some.inj (by
        simpa [Encoding.readNat] using h)
      obtain ⟨hn, hr⟩ := Prod.mk.inj hp
      subst n
      subst rest
      rfl
  | true :: input, n, rest, h => by
      cases hr : Encoding.readNat input with
      | none => simp [Encoding.readNat, hr] at h
      | some result =>
          rcases result with ⟨m, tail⟩
          have hp : (m + 1, tail) = (n, rest) := Option.some.inj (by
            simpa [Encoding.readNat, hr] using h)
          obtain ⟨hn, ht⟩ := Prod.mk.inj hp
          subst n
          subst rest
          have hi := nat_input_shape input m tail hr
          simpa [Encoding.encodeNat, List.replicate_succ] using
            congrArg (List.cons true) hi

/-- Successful frame parsing also identifies the exact consumed prefix. -/
theorem frame_input_shape : (input bits rest : List Bool) →
    Encoding.readFrame input = some (bits, rest) → input = Encoding.frame bits ++ rest
  | [], bits, rest, h => by simp [Encoding.readFrame] at h
  | false :: input, bits, rest, h => by
      have hp : ([], input) = (bits, rest) := Option.some.inj (by
        simpa [Encoding.readFrame] using h)
      obtain ⟨hb, hr⟩ := Prod.mk.inj hp
      subst bits
      subst rest
      rfl
  | true :: [], bits, rest, h => by simp [Encoding.readFrame] at h
  | true :: b :: input, bits, rest, h => by
      cases hr : Encoding.readFrame input with
      | none => simp [Encoding.readFrame, hr] at h
      | some result =>
          rcases result with ⟨more, tail⟩
          have hp : (b :: more, tail) = (bits, rest) := Option.some.inj (by
            simpa [Encoding.readFrame, hr] using h)
          obtain ⟨hb, ht⟩ := Prod.mk.inj hp
          subst bits
          subst rest
          have hi := frame_input_shape input more tail hr
          simpa [Encoding.frame] using congrArg (fun xs => true :: b :: xs) hi

/-- Actual execution agrees with every successful result of the pure decoder,
not just inputs presented syntactically as encoded values. -/
theorem nat_trace_of_read (input rest output : List Bool) (n : ℕ) (v p : Bool)
    (h : Encoding.readNat input = some (n, rest)) :
    Trace natProgram (4 * n + 4) (cfg (some 0) v p input output)
      (cfg none false true rest (List.replicate n true ++ output)) := by
  rw [nat_input_shape input n rest h]
  exact nat_trace n rest output v p

theorem frame_trace_of_read (input bits rest output : List Bool) (v p : Bool)
    (h : Encoding.readFrame input = some (bits, rest)) :
    Trace frameProgram (6 * bits.length + 4) (cfg (some 0) v p input output)
      (cfg none false true rest (bits.reverse ++ output)) := by
  rw [frame_input_shape input bits rest h]
  exact frame_trace bits rest output v p

/-! ## In-place removal of one escape frame -/

/-- Move the reversed payload back onto the input stack. -/
abbrev restoreProgram : Program 2 2 4 :=
  StackRoutines.transferProgram 1 0 0 1

theorem restore_trace (input output : List Bool) (v p : Bool) :
    Trace restoreProgram (3 * output.length + 3)
      (cfg (some 0) v p input output)
      (cfg none false false (output.reverse ++ input) []) := by
  have h := StackRoutines.transferProgram_trace (r := 2) (s := 2)
    1 0 0 1 (by decide) (by decide) (pair v p) (pair input output)
  have ht : Trace restoreProgram (3 * output.length + 2)
      (cfg (some 0) v p input output)
      (cfg (some 3) false false (output.reverse ++ input) []) := by
    simpa [restoreProgram, cfg, StackRoutines.transferResult,
      StackRoutines.transferStacks, readRegs] using h
  have hh : step restoreProgram (cfg (some 3) false false (output.reverse ++ input) []) =
      some (cfg none false false (output.reverse ++ input) []) := by
    simp [step, cfg, execInstr]
  simpa [Nat.add_assoc] using ht.trans (.cons hh (.refl _))

/-- Eleven fixed labels implement one complete in-place frame removal. -/
abbrev unframeProgram : Program 2 2 11 := ProgramLinking.link frameProgram restoreProgram

/-- The linked finite table restores forward order and clears its scratch stack. -/
theorem unframe_trace (bits rest : List Bool) (v p : Bool) :
    Trace unframeProgram (9 * bits.length + 7)
      (cfg (some 0) v p (Encoding.frame bits ++ rest) [])
      (cfg none false false (bits ++ rest) []) := by
  have hp : Trace frameProgram (6 * bits.length + 4)
      (cfg (some 0) v p (Encoding.frame bits ++ rest) [])
      (cfg none false true rest bits.reverse) := by
    simpa using frame_trace bits rest [] v p
  have hq : Trace restoreProgram (3 * bits.length + 3)
      (ProgramLinking.enter restoreProgram (cfg (l := 7) none false true rest bits.reverse))
      (cfg none false false (bits ++ rest) []) := by
    simpa [ProgramLinking.enter, restoreProgram, StackRoutines.transferProgram, cfg]
      using restore_trace rest bits.reverse false true
  have h := ProgramLinking.link_trace frameProgram restoreProgram hp rfl hq
  have hc : (6 * bits.length + 4) + (3 * bits.length + 3) = 9 * bits.length + 7 := by omega
  have hzero : Fin.castAdd 4 (0 : Fin 7) = (0 : Fin 11) := rfl
  simpa only [hc, unframeProgram, ProgramLinking.relabelCfg, ProgramLinking.relocatePc,
    hzero, cfg]
    using h

theorem unframe_runsIn (bits rest : List Bool) (v p : Bool) :
    RunsIn unframeProgram (9 * bits.length + 7)
      (cfg (some 0) v p (Encoding.frame bits ++ rest) [])
      (cfg none false false (bits ++ rest) []) :=
  ⟨_, le_rfl, unframe_trace bits rest v p⟩

/-- The in-place decoder is a complete program on actual raw input, with
canonical output on its designated stack and every register/scratch stack clear. -/
theorem unframe_complete_trace (bits rest : List Bool) :
    Trace unframeProgram (9 * bits.length + 7)
      (initial unframeProgram (Encoding.frame bits ++ rest))
      (terminal unframeProgram (bits ++ rest)) := by
  have hi : initial unframeProgram (Encoding.frame bits ++ rest) =
      cfg (some 0) false false (Encoding.frame bits ++ rest) [] := by
    simp [initial, cfg ]
    constructor <;> funext i <;> fin_cases i <;> rfl
  have ht : terminal unframeProgram (bits ++ rest) =
      cfg none false false (bits ++ rest) [] := by
    simp [terminal, cfg ]
    constructor <;> funext i <;> fin_cases i <;> rfl
  rw [hi, ht]
  exact unframe_trace bits rest false false

theorem nat_runsIn_inputLength (n : ℕ) (rest output : List Bool) (v p : Bool) :
    RunsIn natProgram (4 * (Encoding.encodeNat n ++ rest).length)
      (cfg (some 0) v p (Encoding.encodeNat n ++ rest) output)
      (cfg none false true rest (List.replicate n true ++ output)) := by
  refine ⟨4 * n + 4, ?_, nat_trace n rest output v p⟩
  simp only [List.length_append, Encoding.length_encodeNat]
  omega

theorem frame_runsIn_inputLength (bits rest output : List Bool) (v p : Bool) :
    RunsIn frameProgram (3 * (Encoding.frame bits ++ rest).length + 1)
      (cfg (some 0) v p (Encoding.frame bits ++ rest) output)
      (cfg none false true rest (bits.reverse ++ output)) := by
  refine ⟨6 * bits.length + 4, ?_, frame_trace bits rest output v p⟩
  simp only [List.length_append, Encoding.length_frame]
  omega

theorem unframe_runsIn_inputLength (bits rest : List Bool) (v p : Bool) :
    RunsIn unframeProgram (5 * (Encoding.frame bits ++ rest).length + 2)
      (cfg (some 0) v p (Encoding.frame bits ++ rest) [])
      (cfg none false false (bits ++ rest) []) := by
  refine ⟨9 * bits.length + 7, ?_, unframe_trace bits rest v p⟩
  simp only [List.length_append, Encoding.length_frame]
  omega

/-! The compiler turns the preceding actual instruction traces into actual
primitive tape executions. Each overhead below belongs to one fixed program. -/

theorem nat_primitive_execution (n : ℕ) (rest output : List Bool) (v p : Bool) :
    Computation.RunsIn (primitive natProgram).step
      (primitiveOverhead natProgram * (4 * n + 4))
      (primitiveCfg natProgram (cfg (some 0) v p (Encoding.encodeNat n ++ rest) output))
      (primitiveCfg natProgram
        (cfg none false true rest (List.replicate n true ++ output))) :=
  primitive_trace natProgram (nat_trace n rest output v p)

theorem frame_primitive_execution (bits rest output : List Bool) (v p : Bool) :
    Computation.RunsIn (primitive frameProgram).step
      (primitiveOverhead frameProgram * (6 * bits.length + 4))
      (primitiveCfg frameProgram (cfg (some 0) v p (Encoding.frame bits ++ rest) output))
      (primitiveCfg frameProgram (cfg none false true rest (bits.reverse ++ output))) :=
  primitive_trace frameProgram (frame_trace bits rest output v p)

/-- A complete primitive-tape execution from the actual raw input tape. -/
theorem unframe_primitive_execution (bits rest : List Bool) :
    Computation.RunsIn (primitive unframeProgram).step
      (primitiveOverhead unframeProgram * (9 * bits.length + 7))
      ((primitive unframeProgram).init (Encoding.frame bits ++ rest))
      (primitiveCfg unframeProgram (terminal unframeProgram (bits ++ rest))) := by
  simpa only [primitive_initial] using
    primitive_trace unframeProgram (unframe_complete_trace bits rest)

theorem unframe_bitMachine_outputs (bits rest : List Bool) :
    (bitMachine unframeProgram).OutputsInTime
      (Encoding.frame bits ++ rest) (bits ++ rest) (9 * bits.length + 7) :=
  bitMachine_outputs unframeProgram ⟨_, le_rfl, unframe_complete_trace bits rest⟩

end SubexponentialSAT.ParserProgram

end OAI.Algorithms

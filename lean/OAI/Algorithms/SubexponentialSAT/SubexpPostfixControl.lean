import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BitProgram
import OAI.Algorithms.SubexponentialSAT.Encoding
import OAI.Algorithms.SubexponentialSAT.Algorithm
import OAI.Algorithms.SubexponentialSAT.ParserProgram
import OAI.Algorithms.SubexponentialSAT.ProgramLinking

namespace OAI.Algorithms

/-!
# Concrete postfix instruction dispatch and literal push

The fixed prefix tags are push `0`, add `10`, and multiply `11`.
A push tag is followed by an `Encoding.frame` coefficient payload. End of
the code stack ends the instruction stream. The base dispatcher exposes
explicit service exits. The linked program implements literal push through
the actual frame parser and a Boolean-stack encoding loop; scalar arithmetic
remains at explicit service boundaries.

Registers: 0 last bit, 1 successful-pop flag, 2 binary-operation flag.
Stacks: 0 serialized code, 1 unary operand depth, 2 framed operand data.
The operand data stack is preserved throughout dispatch. On a successful
dispatch the depth stack has already been adjusted for the pending service.
The linked literal service uses stack 3 as initially empty scratch and returns
to dispatch with that scratch empty and the framed operand list updated.
-/

namespace SubexponentialSAT.SubexpPostfixControl

open BitProgram

abbrev triple {α : Type*} (a b c : α) : Fin 3 → α :=
  fun i => if i = 0 then a else if i = 1 then b else c

@[simp] theorem triple_zero {α : Type*} (a b c : α) : triple a b c 0 = a := rfl
@[simp] theorem triple_one {α : Type*} (a b c : α) : triple a b c 1 = b := rfl
@[simp] theorem triple_two {α : Type*} (a b c : α) : triple a b c 2 = c := rfl

@[simp] theorem update_triple_zero {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 0 d = triple d b c := by
  funext i
  fin_cases i <;> simp [triple]

@[simp] theorem update_triple_one {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 1 d = triple a d c := by
  funext i
  fin_cases i <;> simp [triple]

@[simp] theorem update_triple_two {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 2 d = triple a b d := by
  funext i
  fin_cases i <;> simp [triple]

def cfg (pc : Option (Fin 20)) (value present operation : Bool)
    (code depth operands : List Bool) : Cfg 3 3 20 :=
  ⟨pc, triple value present operation, triple code depth operands⟩

/-- Entry to a payload parser followed by a framed operand push. -/
def pushService : Fin 20 := 15
/-- Entry to the scalar addition service on the top two framed operands. -/
def addService : Fin 20 := 16
/-- Entry to the scalar multiplication service on the top two framed operands. -/
def mulService : Fin 20 := 17
def doneExit : Fin 20 := 18
def errorExit : Fin 20 := 19

/-- Twenty labels, three one-bit registers, and three Boolean stacks. -/
abbrev program : Program 3 3 20 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .branch 1 2 doneExit
    | 2 => .branch 0 5 3
    | 3 => .set 0 true 4
    | 4 => .push 1 0 pushService
    | 5 => .pop 0 0 1 6
    | 6 => .branch 1 7 errorExit
    | 7 => .copy 2 0 8
    | 8 => .pop 1 0 1 9
    | 9 => .branch 1 10 errorExit
    | 10 => .pop 1 0 1 11
    | 11 => .branch 1 12 errorExit
    | 12 => .set 0 true 13
    | 13 => .push 1 0 14
    | 14 => .branch 2 mulService addService
    | _ => .halt

@[simp] theorem pushService_halt : program.code pushService = .halt := rfl
@[simp] theorem addService_halt : program.code addService = .halt := rfl
@[simp] theorem mulService_halt : program.code mulService = .halt := rfl
@[simp] theorem doneExit_halt : program.code doneExit = .halt := rfl
@[simp] theorem errorExit_halt : program.code errorExit = .halt := rfl

theorem tag_pop (b v p op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 0) v p op (b :: code) depth operands) =
      some (cfg (some 1) b true op code depth operands) := by
  simp [step, cfg, execInstr, readRegs]

theorem tag_present (v op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 1) v true op code depth operands) =
      some (cfg (some 2) v true op code depth operands) := by
  simp [step, cfg, execInstr]

theorem push_tag (op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 2) false true op code depth operands) =
      some (cfg (some 3) false true op code depth operands) := by
  simp [step, cfg, execInstr]

theorem push_set (op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 3) false true op code depth operands) =
      some (cfg (some 4) true true op code depth operands) := by
  simp [step, cfg, execInstr]

theorem push_depth (op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 4) true true op code depth operands) =
      some (cfg (some pushService) true true op code (true :: depth) operands) := by
  simp [step, cfg, execInstr]

/-- Five actual transitions decode push and reserve one new operand slot. -/
theorem prepare_push_trace (v p op : Bool) (code depth operands : List Bool) :
    Trace program 5 (cfg (some 0) v p op (false :: code) depth operands)
      (cfg (some pushService) true true op code (true :: depth) operands) :=
  .cons (tag_pop false v p op code depth operands)
    (.cons (tag_present false op code depth operands)
      (.cons (push_tag op code depth operands)
        (.cons (push_set op code depth operands)
          (.cons (push_depth op code depth operands) (.refl _)))))

theorem binary_tag (op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 2) true true op code depth operands) =
      some (cfg (some 5) true true op code depth operands) := by
  simp [step, cfg, execInstr]

theorem operation_pop (b v p op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 5) v p op (b :: code) depth operands) =
      some (cfg (some 6) b true op code depth operands) := by
  simp [step, cfg, execInstr, readRegs]

theorem operation_present (b op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 6) b true op code depth operands) =
      some (cfg (some 7) b true op code depth operands) := by
  simp [step, cfg, execInstr]

theorem operation_copy (b op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 7) b true op code depth operands) =
      some (cfg (some 8) b true b code depth operands) := by
  simp [step, cfg, execInstr]

theorem first_operand_pop (a v p op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 8) v p op code (a :: depth) operands) =
      some (cfg (some 9) a true op code depth operands) := by
  simp [step, cfg, execInstr, readRegs]

theorem first_operand_present (a op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 9) a true op code depth operands) =
      some (cfg (some 10) a true op code depth operands) := by
  simp [step, cfg, execInstr]

theorem second_operand_pop (a v p op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 10) v p op code (a :: depth) operands) =
      some (cfg (some 11) a true op code depth operands) := by
  simp [step, cfg, execInstr, readRegs]

theorem second_operand_present (a op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 11) a true op code depth operands) =
      some (cfg (some 12) a true op code depth operands) := by
  simp [step, cfg, execInstr]

theorem result_set (a op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 12) a true op code depth operands) =
      some (cfg (some 13) true true op code depth operands) := by
  simp [step, cfg, execInstr]

theorem result_push (op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 13) true true op code depth operands) =
      some (cfg (some 14) true true op code (true :: depth) operands) := by
  simp [step, cfg, execInstr]

theorem operation_dispatch (op : Bool) (code depth operands : List Bool) :
    step program (cfg (some 14) true true op code depth operands) =
      some (cfg (some (if op then mulService else addService)) true true op code depth operands) := by
  simp [step, cfg, execInstr]

/-- Thirteen actual transitions prepare either binary operation and check depth two. -/
theorem prepare_binary_trace (b a₀ a₁ v p op : Bool) (code depth operands : List Bool) :
    Trace program 13
      (cfg (some 0) v p op (true :: b :: code) (a₀ :: a₁ :: depth) operands)
      (cfg (some (if b then mulService else addService)) true true b code (true :: depth) operands) :=
  .cons (tag_pop true v p op (b :: code) (a₀ :: a₁ :: depth) operands)
    (.cons (tag_present true op (b :: code) (a₀ :: a₁ :: depth) operands)
      (.cons (binary_tag op (b :: code) (a₀ :: a₁ :: depth) operands)
        (.cons (operation_pop b true true op code (a₀ :: a₁ :: depth) operands)
          (.cons (operation_present b op code (a₀ :: a₁ :: depth) operands)
            (.cons (operation_copy b op code (a₀ :: a₁ :: depth) operands)
              (.cons (first_operand_pop a₀ b true b code (a₁ :: depth) operands)
                (.cons (first_operand_present a₀ b code (a₁ :: depth) operands)
                  (.cons (second_operand_pop a₁ a₀ true b code depth operands)
                    (.cons (second_operand_present a₁ b code depth operands)
                      (.cons (result_set a₁ b code depth operands)
                        (.cons (result_push b code depth operands)
                          (.cons (operation_dispatch b code (true :: depth) operands) (.refl _)))))))))))))

/-- The common six-step tag decoder ends before accessing the operand-depth stack. -/
theorem binary_prefix_trace (b v p op : Bool) (code depth operands : List Bool) :
    Trace program 6 (cfg (some 0) v p op (true :: b :: code) depth operands)
      (cfg (some 8) b true b code depth operands) :=
  .cons (tag_pop true v p op (b :: code) depth operands)
    (.cons (tag_present true op (b :: code) depth operands)
      (.cons (binary_tag op (b :: code) depth operands)
        (.cons (operation_pop b true true op code depth operands)
          (.cons (operation_present b op code depth operands)
            (.cons (operation_copy b op code depth operands) (.refl _))))))

/-- Empty code is a completed instruction stream, not a malformed tag. -/
theorem eof_trace (v p op : Bool) (depth operands : List Bool) :
    Trace program 2 (cfg (some 0) v p op [] depth operands)
      (cfg (some doneExit) false false op [] depth operands) := by
  refine .cons (b := cfg (some 1) false false op [] depth operands) ?_ ?_
  · simp [step, cfg, execInstr, readRegs]
  · refine .cons ?_ (.refl _)
    simp [step, cfg, execInstr]

/-- A leading one must be followed by an operation bit. -/
theorem truncated_tag_trace (v p op : Bool) (depth operands : List Bool) :
    Trace program 5 (cfg (some 0) v p op [true] depth operands)
      (cfg (some errorExit) false false op [] depth operands) := by
  refine .cons (tag_pop true v p op [] depth operands)
    (.cons (tag_present true op [] depth operands)
      (.cons (binary_tag op [] depth operands) ?_))
  refine .cons (b := cfg (some 6) false false op [] depth operands) ?_ ?_
  · simp [step, cfg, execInstr, readRegs]
  · refine .cons ?_ (.refl _)
    simp [step, cfg, execInstr]

/-- Binary instructions reject an empty operand stack in eight measured steps. -/
theorem empty_depth_trace (b v p op : Bool) (code operands : List Bool) :
    Trace program 8 (cfg (some 0) v p op (true :: b :: code) [] operands)
      (cfg (some errorExit) false false b code [] operands) := by
  have suffix : Trace program 2 (cfg (some 8) b true b code [] operands)
      (cfg (some errorExit) false false b code [] operands) := by
    refine .cons (b := cfg (some 9) false false b code [] operands) ?_ ?_
    · simp [step, cfg, execInstr, readRegs]
    · refine .cons ?_ (.refl _)
      simp [step, cfg, execInstr]
  exact (binary_prefix_trace b v p op code [] operands).trans suffix

/-- The second explicit pop rejects depth one before any arithmetic service. -/
theorem singleton_depth_trace (b a v p op : Bool) (code operands : List Bool) :
    Trace program 10 (cfg (some 0) v p op (true :: b :: code) [a] operands)
      (cfg (some errorExit) false false b code [] operands) := by
  have suffix : Trace program 4 (cfg (some 8) b true b code [a] operands)
      (cfg (some errorExit) false false b code [] operands) := by
    refine .cons (first_operand_pop a b true b code [] operands)
      (.cons (first_operand_present a b code [] operands) ?_)
    refine .cons (b := cfg (some 11) false false b code [] operands) ?_ ?_
    · simp [step, cfg, execInstr, readRegs]
    · refine .cons ?_ (.refl _)
      simp [step, cfg, execInstr]
  exact (binary_prefix_trace b v p op code [a] operands).trans suffix

/-- Dispatch never treats a scalar operation as a primitive write to operand data. -/
theorem step_preserves_operands {a b : Cfg 3 3 20}
    (h : step program a = some b) : b.stacks 2 = a.stacks 2 := by
  cases hp : a.pc with
  | none => simp [step, hp] at h
  | some pc =>
      have hb : execInstr (program.code pc) a = b := by
        simpa [step, hp] using h
      rw [← hb]
      fin_cases pc <;> simp [ execInstr]

theorem trace_preserves_operands {n : ℕ} {a b : Cfg 3 3 20}
    (h : Trace program n a b) : b.stacks 2 = a.stacks 2 := by
  induction h with
  | refl => rfl
  | cons hs ht ih => exact ih.trans (step_preserves_operands hs)

/-! ## Serialization of the existing postfix instruction type -/

def serializeInstr {R : Type*} (encode : R → List Bool) : Algorithm.Instr R → List Bool
  | .push x => false :: Encoding.frame (encode x)
  | .add => [true, false]
  | .mul => [true, true]

def serializeCode {R : Type*} (encode : R → List Bool) : List (Algorithm.Instr R) → List Bool
  | [] => []
  | i :: is => serializeInstr encode i ++ serializeCode encode is

def operandDepth {R : Type*} (xs : List R) : List Bool :=
  List.replicate xs.length true

def serializeOperands {R : Type*} (encode : R → List Bool) : List R → List Bool
  | [] => [false]
  | x :: xs => true :: (Encoding.frame (encode x) ++ serializeOperands encode xs)

/-- At the push boundary the parser sees exactly one coefficient frame and the code suffix. -/
theorem serialized_push_trace {R : Type*} (encode : R → List Bool)
    (x : R) (is : List (Algorithm.Instr R)) (xs : List R) (v p op : Bool) :
    Trace program 5
      (cfg (some 0) v p op (serializeCode encode (.push x :: is))
        (operandDepth xs) (serializeOperands encode xs))
      (cfg (some pushService) true true op (Encoding.frame (encode x) ++ serializeCode encode is)
        (operandDepth (x :: xs)) (serializeOperands encode xs)) := by
  simpa [serializeCode, serializeInstr, operandDepth, List.replicate_succ] using
    prepare_push_trace v p op (Encoding.frame (encode x) ++ serializeCode encode is)
      (operandDepth xs) (serializeOperands encode xs)

/-- Arithmetic remains pending: only its tag and the two-operand guard have executed. -/
theorem serialized_add_trace {R : Type*} (encode : R → List Bool)
    (x y : R) (is : List (Algorithm.Instr R)) (xs : List R) (v p op : Bool) :
    Trace program 13
      (cfg (some 0) v p op (serializeCode encode (.add :: is))
        (operandDepth (y :: x :: xs)) (serializeOperands encode (y :: x :: xs)))
      (cfg (some addService) true true false (serializeCode encode is)
        (true :: operandDepth xs) (serializeOperands encode (y :: x :: xs))) := by
  simpa [serializeCode, serializeInstr, operandDepth, List.replicate_succ] using
    prepare_binary_trace false true true v p op (serializeCode encode is)
      (operandDepth xs) (serializeOperands encode (y :: x :: xs))

theorem serialized_mul_trace {R : Type*} (encode : R → List Bool)
    (x y : R) (is : List (Algorithm.Instr R)) (xs : List R) (v p op : Bool) :
    Trace program 13
      (cfg (some 0) v p op (serializeCode encode (.mul :: is))
        (operandDepth (y :: x :: xs)) (serializeOperands encode (y :: x :: xs)))
      (cfg (some mulService) true true true (serializeCode encode is)
        (true :: operandDepth xs) (serializeOperands encode (y :: x :: xs))) := by
  simpa [serializeCode, serializeInstr, operandDepth, List.replicate_succ] using
    prepare_binary_trace true true true v p op (serializeCode encode is)
      (operandDepth xs) (serializeOperands encode (y :: x :: xs))

/-! ## Literal-push service with the framed-list operand ABI -/

abbrev quadruple {α : Type*} (a b c d : α) : Fin 4 → α :=
  fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d

@[simp] theorem quadruple_zero {α : Type*} (a b c d : α) : quadruple a b c d 0 = a := rfl
@[simp] theorem quadruple_one {α : Type*} (a b c d : α) : quadruple a b c d 1 = b := rfl
@[simp] theorem quadruple_two {α : Type*} (a b c d : α) : quadruple a b c d 2 = c := rfl
@[simp] theorem quadruple_three {α : Type*} (a b c d : α) : quadruple a b c d 3 = d := rfl

@[simp] theorem update_quadruple_zero {α : Type*} (a b c d e : α) :
    Function.update (quadruple a b c d) 0 e = quadruple e b c d := by
  funext i; fin_cases i <;> simp [quadruple]
@[simp] theorem update_quadruple_one {α : Type*} (a b c d e : α) :
    Function.update (quadruple a b c d) 1 e = quadruple a e c d := by
  funext i; fin_cases i <;> simp [quadruple]
@[simp] theorem update_quadruple_two {α : Type*} (a b c d e : α) :
    Function.update (quadruple a b c d) 2 e = quadruple a b e d := by
  funext i; fin_cases i <;> simp [quadruple]
@[simp] theorem update_quadruple_three {α : Type*} (a b c d e : α) :
    Function.update (quadruple a b c d) 3 e = quadruple a b c e := by
  funext i; fin_cases i <;> simp [quadruple]

abbrev cfg4 {l : ℕ} (pc : Option (Fin l)) (value present operation : Bool)
    (code depth operands scratch : List Bool) : Cfg 3 4 l :=
  ⟨pc, triple value present operation, quadruple code depth operands scratch⟩

private theorem cfg_ext {r s l : ℕ} {a b : Cfg r s l}
    (hp : a.pc = b.pc) (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

def parserRegister : Fin 2 → Fin 3 := Fin.castAdd 1
def parserStack (i : Fin 2) : Fin 4 := if i = 0 then 0 else 3
def parserLabel : Fin 7 → Fin 17 := Fin.castAdd 10

theorem parserRegister_injective : Function.Injective parserRegister := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 3 => i.val) h)

theorem parserStack_injective : Function.Injective parserStack := by decide

/-- The first seven labels are the actual relocated frame parser. The remaining
labels rebuild the escaped payload from its reverse and add the list cons tag. -/
def literalService : Program 3 4 17 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code := Fin.addCases (motive := fun _ : Fin (7 + 10) => Instr 3 4 17)
    (fun pc : Fin 7 => ProgramLinking.relocateInstr parserRegister parserStack parserLabel
      (some 7) (ParserProgram.frameProgram.code pc))
    (fun pc : Fin 10 => match pc.val with
      | 0 => .set 0 false 8
      | 1 => .push 2 0 9
      | 2 => .pop 3 0 1 10
      | 3 => .branch 1 11 14
      | 4 => .push 2 0 12
      | 5 => .set 0 true 13
      | 6 => .push 2 0 9
      | 7 => .set 0 true 15
      | 8 => .push 2 0 16
      | _ => .halt)

@[simp] private theorem literalService_code7 : literalService.code 7 = .set 0 false 8 := rfl
@[simp] private theorem literalService_code8 : literalService.code 8 = .push 2 0 9 := rfl
@[simp] private theorem literalService_code9 : literalService.code 9 = .pop 3 0 1 10 := rfl
@[simp] private theorem literalService_code10 : literalService.code 10 = .branch 1 11 14 := rfl
@[simp] private theorem literalService_code11 : literalService.code 11 = .push 2 0 12 := rfl
@[simp] private theorem literalService_code12 : literalService.code 12 = .set 0 true 13 := rfl
@[simp] private theorem literalService_code13 : literalService.code 13 = .push 2 0 9 := rfl
@[simp] private theorem literalService_code14 : literalService.code 14 = .set 0 true 15 := rfl
@[simp] private theorem literalService_code15 : literalService.code 15 = .push 2 0 16 := rfl
@[simp] private theorem literalService_code16 : literalService.code 16 = .halt := rfl

theorem literalService_parser_code :
    ProgramLinking.CodeEmbedding ParserProgram.frameProgram literalService
      parserRegister parserStack parserLabel (some 7) := by
  intro pc
  simp [literalService, parserLabel]

private theorem embed_parser_cfg (pc : Option (Fin 7)) (v p op : Bool)
    (code depth operands scratch : List Bool) :
    ProgramLinking.embedCfg parserRegister parserStack parserLabel (some 7)
      (cfg4 none false false op [] depth operands [])
      (ParserProgram.cfg pc v p code scratch) =
    cfg4 (ProgramLinking.relocatePc parserLabel (some 7) pc) v p op code depth operands scratch := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i
    · change Function.extend parserRegister (ParserProgram.pair v p)
        (triple false false op) (parserRegister 0) = v
      rw [parserRegister_injective.extend_apply]
      rfl
    · change Function.extend parserRegister (ParserProgram.pair v p)
        (triple false false op) (parserRegister 1) = p
      rw [parserRegister_injective.extend_apply]
      rfl
    · change Function.extend parserRegister (ParserProgram.pair v p)
        (triple false false op) 2 = op
      rw [Function.extend_apply' _ _ _ (by decide : ¬ ∃ i, parserRegister i = 2)]
      rfl
  · funext i
    fin_cases i
    · change Function.extend parserStack (ParserProgram.pair code scratch)
        (quadruple [] depth operands []) (parserStack 0) = code
      rw [parserStack_injective.extend_apply]
      rfl
    · change Function.extend parserStack (ParserProgram.pair code scratch)
        (quadruple [] depth operands []) 1 = depth
      rw [Function.extend_apply' _ _ _ (by decide : ¬ ∃ i, parserStack i = 1)]
      rfl
    · change Function.extend parserStack (ParserProgram.pair code scratch)
        (quadruple [] depth operands []) 2 = operands
      rw [Function.extend_apply' _ _ _ (by decide : ¬ ∃ i, parserStack i = 2)]
      rfl
    · change Function.extend parserStack (ParserProgram.pair code scratch)
        (quadruple [] depth operands []) (parserStack 1) = scratch
      rw [parserStack_injective.extend_apply]
      rfl

/-- Reuse the measured parser trace through actual instruction-table relocation. -/
theorem literalService_parse_trace (bits rest depth operands scratch : List Bool)
    (v p op : Bool) :
    Trace literalService (6 * bits.length + 4)
      (cfg4 (some 0) v p op (Encoding.frame bits ++ rest) depth operands scratch)
      (cfg4 (some 7) false true op rest depth operands (bits.reverse ++ scratch)) := by
  have h := ProgramLinking.relocate_trace ParserProgram.frameProgram literalService
    parserRegister parserStack parserLabel (some 7)
    (cfg4 none false false op [] depth operands [])
    parserRegister_injective parserStack_injective literalService_parser_code
    (ParserProgram.frame_trace bits rest scratch v p)
  rw [embed_parser_cfg, embed_parser_cfg] at h
  have hz : parserLabel (0 : Fin 7) = (0 : Fin 17) := by
    apply Fin.ext
    rfl
  simpa only [ProgramLinking.relocatePc, hz] using h

/-- Escaped data without the final false delimiter. -/
def escapeBits : List Bool → List Bool
  | [] => []
  | b :: bs => true :: b :: escapeBits bs

theorem escapeBits_append (a b : List Bool) :
    escapeBits (a ++ b) = escapeBits a ++ escapeBits b := by
  induction a with
  | nil => rfl
  | cons a as ih => simp [escapeBits, ih]

theorem frame_eq_escape (bits : List Bool) :
    Encoding.frame bits = escapeBits bits ++ [false] := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [Encoding.frame_cons, escapeBits, ih]

theorem literalService_encode_cycle (b v p op : Bool) (code depth operands scratch : List Bool) :
    Trace literalService 5
      (cfg4 (some 9) v p op code depth operands (b :: scratch))
      (cfg4 (some 9) true true op code depth (true :: b :: operands) scratch) := by
  refine .cons (b := cfg4 (some 10) b true op code depth operands scratch) ?_ ?_
  · simp [step, execInstr, cfg4, triple, quadruple, readRegs]
  refine .cons (b := cfg4 (some 11) b true op code depth operands scratch) ?_ ?_
  · simp [step, execInstr, cfg4, triple, quadruple]
  refine .cons (b := cfg4 (some 12) b true op code depth (b :: operands) scratch) ?_ ?_
  · simp [step, execInstr, cfg4, triple, quadruple]
  refine .cons (b := cfg4 (some 13) true true op code depth (b :: operands) scratch) ?_ ?_
  · simp [step, execInstr, cfg4, triple, quadruple]
  refine .cons ?_ (.refl _)
  simp [step, execInstr, cfg4, triple, quadruple]

theorem literalService_encode_loop (scratch code depth operands : List Bool) (v p op : Bool) :
    Trace literalService (5 * scratch.length + 2)
      (cfg4 (some 9) v p op code depth operands scratch)
      (cfg4 (some 14) false false op code depth (escapeBits scratch.reverse ++ operands) []) := by
  induction scratch generalizing operands v p with
  | nil =>
      refine .cons (b := cfg4 (some 10) false false op code depth operands []) ?_ ?_
      · simp [step, execInstr, cfg4, triple, quadruple, readRegs]
      · refine .cons ?_ (.refl _)
        simp [step, execInstr, cfg4, triple, quadruple, escapeBits]
  | cons b bs ih =>
      have h := (literalService_encode_cycle b v p op code depth operands bs).trans
        (ih (true :: b :: operands) true true)
      have hn : 5 + (5 * bs.length + 2) = 5 * (b :: bs).length + 2 := by
        simp only [List.length_cons]
        omega
      simpa only [hn, List.reverse_cons, escapeBits_append, escapeBits,
        List.append_assoc, List.cons_append, List.nil_append] using h

theorem literalService_encode_trace (bits code depth operands : List Bool) (v p op : Bool) :
    Trace literalService (5 * bits.length + 7)
      (cfg4 (some 7) v p op code depth operands bits.reverse)
      (cfg4 none true false op code depth (true :: (Encoding.frame bits ++ operands)) []) := by
  have init : Trace literalService 2
      (cfg4 (some 7) v p op code depth operands bits.reverse)
      (cfg4 (some 9) false p op code depth (false :: operands) bits.reverse) := by
    refine .cons (b := cfg4 (some 8) false p op code depth operands bits.reverse) ?_ ?_
    · simp [step, execInstr, cfg4, triple, quadruple]
    · refine .cons ?_ (.refl _)
      simp [step, execInstr, cfg4, triple, quadruple]
  have loop := literalService_encode_loop bits.reverse code depth (false :: operands) false p op
  have finish : Trace literalService 3
      (cfg4 (some 14) false false op code depth (Encoding.frame bits ++ operands) [])
      (cfg4 none true false op code depth (true :: (Encoding.frame bits ++ operands)) []) := by
    refine .cons (b := cfg4 (some 15) true false op code depth (Encoding.frame bits ++ operands) []) ?_ ?_
    · simp [step, execInstr, cfg4, triple, quadruple]
    refine .cons (b := cfg4 (some 16) true false op code depth (true :: (Encoding.frame bits ++ operands)) []) ?_ ?_
    · simp [step, execInstr, cfg4, triple, quadruple]
    refine .cons ?_ (.refl _)
    simp [step, execInstr, cfg4, triple, quadruple]
  have loop' : Trace literalService (5 * bits.length + 2)
      (cfg4 (some 9) false p op code depth (false :: operands) bits.reverse)
      (cfg4 (some 14) false false op code depth (Encoding.frame bits ++ operands) []) := by
    simpa [List.length_reverse, List.reverse_reverse, frame_eq_escape,
      List.append_assoc] using loop
  have h := (init.trans loop').trans finish
  have hn : 2 + (5 * bits.length + 2) + 3 = 5 * bits.length + 7 := by omega
  simpa only [hn] using h

/-- Complete literal service: consume one frame and push a framed list item. -/
theorem literalService_trace (bits rest depth operands : List Bool) (v p op : Bool) :
    Trace literalService (11 * bits.length + 11)
      (cfg4 (some 0) v p op (Encoding.frame bits ++ rest) depth operands [])
      (cfg4 none true false op rest depth (true :: (Encoding.frame bits ++ operands)) []) := by
  have parse := literalService_parse_trace bits rest depth operands [] v p op
  have encode := literalService_encode_trace bits rest depth operands false true op
  simp only [List.append_nil] at parse
  have h := parse.trans encode
  have hn : (6 * bits.length + 4) + (5 * bits.length + 7) = 11 * bits.length + 11 := by omega
  simpa only [hn] using h

/-- The control program retains its label range; the literal service follows it. -/
def controlLabel : Fin 20 → Fin 37 := Fin.castAdd 17
def controlStack : Fin 3 → Fin 4 := Fin.castAdd 1
def literalLabel : Fin 17 → Fin 37 := Fin.natAdd 20

/-- Concrete linkage: only push calls the literal service, whose halt is replaced
by a return to dispatch. Add/multiply remain explicit service boundaries. -/
def pushLoopProgram : Program 3 4 37 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code := Fin.addCases (motive := fun _ : Fin (20 + 17) => Instr 3 4 37)
    (fun pc : Fin 20 =>
      if pc = pushService then .goto (literalLabel 0)
      else ProgramLinking.relocateInstr id controlStack controlLabel none (program.code pc))
    (fun pc : Fin 17 =>
      ProgramLinking.relocateInstr id id literalLabel (some 0) (literalService.code pc))

@[simp] private theorem pushLoop_code0 : pushLoopProgram.code 0 = .pop 0 0 1 1 := rfl
@[simp] private theorem pushLoop_code1 : pushLoopProgram.code 1 = .branch 1 2 18 := rfl
@[simp] private theorem pushLoop_code2 : pushLoopProgram.code 2 = .branch 0 5 3 := rfl
@[simp] private theorem pushLoop_code3 : pushLoopProgram.code 3 = .set 0 true 4 := rfl
@[simp] private theorem pushLoop_code4 : pushLoopProgram.code 4 = .push 1 0 15 := rfl
@[simp] private theorem pushLoop_code15 : pushLoopProgram.code 15 = .goto 20 := rfl

theorem pushLoop_literal_code :
    ProgramLinking.CodeEmbedding literalService pushLoopProgram
      id id literalLabel (some 0) := by
  intro pc
  simp [pushLoopProgram, literalLabel]

theorem pushLoop_control_code (pc : Fin 20) (hpc : pc ≠ pushService) :
    pushLoopProgram.code (controlLabel pc) =
      ProgramLinking.relocateInstr id controlStack controlLabel none (program.code pc) := by
  simp [pushLoopProgram, controlLabel, hpc]

/-- The five dispatcher instructions and the actual service-call jump. -/
theorem pushLoop_prepare_trace (v p op : Bool) (code depth operands : List Bool) :
    Trace pushLoopProgram 6
      (cfg4 (some 0) v p op (false :: code) depth operands [])
      (cfg4 (some 20) true true op code (true :: depth) operands []) := by
  refine .cons (b := cfg4 (some 1) false true op code depth operands []) ?_ ?_
  · simp [step, execInstr, cfg4, triple, quadruple, readRegs]
  refine .cons (b := cfg4 (some 2) false true op code depth operands []) ?_ ?_
  · simp [step, execInstr, cfg4, triple, quadruple]
  refine .cons (b := cfg4 (some 3) false true op code depth operands []) ?_ ?_
  · simp [step, execInstr, cfg4, triple, quadruple]
  refine .cons (b := cfg4 (some 4) true true op code depth operands []) ?_ ?_
  · simp [step, execInstr, cfg4, triple, quadruple]
  refine .cons (b := cfg4 (some 15) true true op code (true :: depth) operands []) ?_ ?_
  · simp [step, execInstr, cfg4, triple, quadruple]
  refine .cons ?_ (.refl _)
  simp [step, execInstr, cfg4, triple, quadruple]

/-- The source service's halt is the linked program's actual return jump. -/
theorem pushLoop_service_trace (bits rest depth operands : List Bool) (v p op : Bool) :
    Trace pushLoopProgram (11 * bits.length + 11)
      (cfg4 (some 20) v p op (Encoding.frame bits ++ rest) depth operands [])
      (cfg4 (some 0) true false op rest depth (true :: (Encoding.frame bits ++ operands)) []) := by
  have h := ProgramLinking.relocate_trace literalService pushLoopProgram
    id id literalLabel (some 0) (cfg4 none false false op [] depth operands [])
    Function.injective_id Function.injective_id pushLoop_literal_code
    (literalService_trace bits rest depth operands v p op)
  rw [ProgramLinking.embedCfg_id, ProgramLinking.embedCfg_id] at h
  exact h

/-- Full measured push instruction: consumes its tag and complete payload,
updates the framed operand list and depth, clears scratch, and returns to dispatch. -/
theorem pushLoop_literal_trace (bits rest depth operands : List Bool) (v p op : Bool) :
    Trace pushLoopProgram (11 * bits.length + 17)
      (cfg4 (some 0) v p op (false :: (Encoding.frame bits ++ rest)) depth operands [])
      (cfg4 (some 0) true false op rest (true :: depth)
        (true :: (Encoding.frame bits ++ operands)) []) := by
  have h := (pushLoop_prepare_trace v p op (Encoding.frame bits ++ rest) depth operands).trans
    (pushLoop_service_trace bits rest (true :: depth) operands true true op)
  have hn : 6 + (11 * bits.length + 11) = 11 * bits.length + 17 := by omega
  simpa only [hn] using h

theorem serializeOperands_eq {R : Type*} (encode : R → List Bool) (xs : List R) :
    serializeOperands encode xs = Encoding.encodeList encode xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [serializeOperands, Encoding.encodeList, ih]

/-- A genuine implementation of a source postfix push under the framed-list ABI. -/
theorem serialized_push_complete_trace {R : Type*} (encode : R → List Bool)
    (x : R) (is : List (Algorithm.Instr R)) (xs : List R) (v p op : Bool) :
    Trace pushLoopProgram (11 * (encode x).length + 17)
      (cfg4 (some 0) v p op (serializeCode encode (.push x :: is))
        (operandDepth xs) (Encoding.encodeList encode xs) [])
      (cfg4 (some 0) true false op (serializeCode encode is)
        (operandDepth (x :: xs)) (Encoding.encodeList encode (x :: xs)) []) := by
  simpa [serializeCode, serializeInstr, operandDepth, Encoding.encodeList,
    List.replicate_succ] using
    pushLoop_literal_trace (encode x) (serializeCode encode is) (operandDepth xs)
      (Encoding.encodeList encode xs) v p op

end SubexponentialSAT.SubexpPostfixControl

end OAI.Algorithms

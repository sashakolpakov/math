import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpKernelControl
import OAI.Algorithms.SubexponentialSAT.SubexpHornerSource
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-!
# A fixed source constructor for a prepared interpolation table

Rows contain literal payloads and coordinate records containing a literal
input and a list of coefficient payloads. No record contains source code.
The controller runs the concrete Horner emitter and assembles the surrounding
right-associated products and sum. Cache selection and scalar literal
preparation are separate from this prepared-data interface.
-/

namespace SubexponentialSAT.SubexpTableSource

open BitProgram StructuredCalls
open SubexpKernelControl (Word Accumulator pushWord operator operators emit bump
  setCounter counterWord)

structure Coordinate where
  input : Word
  coefficients : List Word

structure Row where
  value : Word
  coordinates : List Coordinate

def encodeCoordinate (c : Coordinate) : Word :=
  Encoding.frame c.input ++ Encoding.encodeList id c.coefficients

def encodeRow (r : Row) : Word :=
  Encoding.frame r.value ++ Encoding.encodeList encodeCoordinate r.coordinates

def encodeRows (rs : List Row) : Word := Encoding.encodeList encodeRow rs

def coordinateCode (zero : Word) (c : Coordinate) : Word :=
  SubexpHornerSource.source c.input zero c.coefficients

def rowCode (zero one : Word) (r : Row) : Word :=
  pushWord r.value ++ (r.coordinates.map (coordinateCode zero)).flatten ++
    pushWord one ++ operators true r.coordinates.length ++ operator true

def tableCode (zero one : Word) (rs : List Row) : Word :=
  (rs.map (rowCode zero one)).flatten ++ pushWord zero ++ operators false rs.length

def ofRow {R A : Type*} {p k : ℕ} (encode : A → Word) (literal : R → A)
    (cache : List (List R)) (inputs : Fin k → A)
    (row : SubexpTableInterpolation.Row p k R) : Row :=
  ⟨encode (literal row.value), List.ofFn fun i : Fin k =>
    ⟨encode (inputs i),
      (cache.getD (row.labels.get i).val []).map (fun a => encode (literal a))⟩⟩

theorem coordinateCode_eq {R A : Type*} [Zero A]
    (encode : A → Word) (literal : R → A) (x : A) (cs : List R) :
    coordinateCode (encode 0) ⟨encode x, cs.map (fun a => encode (literal a))⟩ =
      SubexpPostfixControl.serializeCode encode
        (SubexpTableInterpolation.hornerExpr literal (.lit x) cs).compile :=
  SubexpHornerSource.source_eq_serialize encode literal x cs

theorem rowCode_eq {R A : Type*} [Zero A] [One A] {p k : ℕ}
    (encode : A → Word) (literal : R → A) (cache : List (List R))
    (inputs : Fin k → A) (row : SubexpTableInterpolation.Row p k R) :
    rowCode (encode 0) (encode 1) (ofRow encode literal cache inputs row) =
      SubexpPostfixControl.serializeCode encode
        (SubexpTableInterpolation.rowExpr literal cache row (fun i => .lit (inputs i))).compile := by
  simp [rowCode, ofRow, SubexpTableInterpolation.rowExpr, Algorithm.Expr.compile,
    SubexpKernelControl.serializeCode_append, SubexpKernelControl.compile_product,
    SubexpPostfixControl.serializeCode, SubexpPostfixControl.serializeInstr,
    coordinateCode_eq, pushWord, operator, List.map_ofFn, Function.comp_def,
    List.append_assoc]

theorem tableCode_eq {R A : Type*} [Zero A] [One A] {p k : ℕ}
    (encode : A → Word) (literal : R → A) (cache : List (List R))
    (inputs : Fin k → A) (rows : List (SubexpTableInterpolation.Row p k R)) :
    tableCode (encode 0) (encode 1) (rows.map (ofRow encode literal cache inputs)) =
      SubexpPostfixControl.serializeCode encode
        (SubexpTableInterpolation.tableExpr literal cache rows (fun i => .lit (inputs i))).compile := by
  simp [tableCode, SubexpTableInterpolation.tableExpr, SubexpKernelControl.compile_sum,
    List.map_map, Function.comp_def, rowCode_eq]

/-! The first eight ports have the kernel constructor's existing convention.
The three additional ports hold Horner output, its accumulator, and its
pending-operator counter. Port 7 temporarily holds the coordinate input. -/

def firstEight (i : Fin 8) : Fin 11 := Fin.castAdd 3 i

def work (v p c : Bool) (input zero one : Word) (a : Accumulator)
    (scratch ce code hornerAcc hornerCount : Word) : State 3 11 :=
  ⟨SubexpHornerProgram.triple v p c,
    ![input, zero, one, a.output, scratch, a.outer, a.groups, ce,
      code, hornerAcc, hornerCount]⟩

def state (v p : Bool) (input zero one : Word) (a : Accumulator) : State 3 11 :=
  work v p true input zero one a [] a.terms [] [] []

abbrev baseCall (cmd : Cmd 3 8) : Cmd 3 11 :=
  .call (ProgramLinking.liftProgram (StructuredCalls.compiled cmd 0 3) id firstEight)

theorem embed_base (v p v' p' : Bool) (input zero one input' zero' one' : Word)
    (a a' : Accumulator) :
    embedState id firstEight (state v p input zero one a)
      (SubexpKernelControl.state v' p' input' zero' one' a') =
      state v' p' input' zero' one' a' := by
  apply embedState_eq_of_ports
  · exact Function.injective_id
  · intro i j h; exact Fin.ext (congrArg (fun x : Fin 11 => x.val) h)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have hout : 8 ≤ i.val := by
      by_contra hn
      exact hi ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
    fin_cases i <;> simp_all [state, work]

theorem base_eval {cmd : Cmd 3 8} {n : ℕ} {v p v' p' : Bool}
    {input zero one input' zero' one' : Word} {a a' : Accumulator}
    (h : Eval cmd n (SubexpKernelControl.state v p input zero one a)
      (SubexpKernelControl.state v' p' input' zero' one' a')) :
    Eval (baseCall cmd) (n + 1) (state v p input zero one a)
      (state v' p' input' zero' one' a') := by
  have ht := eval_call_lifted (StructuredCalls.compiled cmd 0 3) id firstEight
    (state v p input zero one a) Function.injective_id
    (by intro i j h; exact Fin.ext (congrArg (fun x : Fin 11 => x.val) h))
    (StructuredCalls.compiled_halt_trace h 0 3)
  simpa only [baseCall, embed_base] using ht

private abbrev atom (a : StructuredProgram.Atom 3 11) : Cmd 3 11 := .base (.atom a)
local infixr:60 " ;; " => Cmd.seq

abbrev popTag : Cmd 3 11 := baseCall SubexpKernelControl.popTag
abbrev unframe : Cmd 3 11 := baseCall SubexpKernelControl.unframe
abbrev emitFramedLiteral : Cmd 3 11 := baseCall SubexpKernelControl.emitFramedLiteral
abbrev emitLiteral (which : Bool) : Cmd 3 11 :=
  baseCall (SubexpKernelControl.emitLiteral (if which then 2 else 1))
abbrev emitOperator (mul : Bool) : Cmd 3 11 := baseCall (SubexpKernelControl.emitOperator mul)
abbrev countOne (i : Fin 3) : Cmd 3 11 :=
  baseCall (SubexpKernelControl.countOne (SubexpKernelControl.counterPort i))
abbrev drain (i : Fin 3) (mul : Bool) : Cmd 3 11 :=
  baseCall (SubexpKernelControl.drain (SubexpKernelControl.counterPort i) mul)

def parserRegs (i : Fin 2) : Fin 3 := Fin.castAdd 1 i
def parserStacks : Fin 2 → Fin 11 := ParserProgram.pair 0 4
abbrev captureInput : Cmd 3 11 :=
  .call (ProgramLinking.liftProgram ParserProgram.frameProgram parserRegs parserStacks)

abbrev transfer (src dst : Fin 11) : Cmd 3 11 :=
  .call (StackRoutines.transferProgram src dst 0 1)
abbrev clear (src : Fin 11) : Cmd 3 11 := .call (StackRoutines.clearProgram src 0 1)

def hornerPorts : Fin 7 → Fin 11 := ![0, 7, 1, 9, 4, 10, 8]
abbrev horner : Cmd 3 11 :=
  .call (ProgramLinking.liftProgram SubexpHornerSource.program id hornerPorts)

abbrev coordinateBody : Cmd 3 11 :=
  captureInput ;; transfer 4 7 ;; horner ;; transfer 8 3 ;; clear 7 ;;
    atom (.set 2 true) ;; countOne 1

abbrev scanLoop (body : Cmd 3 11) : Cmd 3 11 :=
  .while 0 (unframe ;; body ;; popTag)
abbrev scan (body : Cmd 3 11) : Cmd 3 11 := popTag ;; scanLoop body

abbrev rowBody : Cmd 3 11 :=
  emitFramedLiteral ;; scan coordinateBody ;; emitLiteral true ;;
    drain 1 true ;; emitOperator true ;; countOne 0

abbrev table : Cmd 3 11 := scan rowBody ;; emitLiteral false ;; drain 0 false

theorem popTag_eval (b v p : Bool) (input zero one : Word) (a : Accumulator) :
    Eval popTag 2 (state v p (b :: input) zero one a) (state b true input zero one a) :=
  base_eval (SubexpKernelControl.popTag_eval b v p input zero one a)

theorem unframe_eval (v p : Bool) (bits rest zero one : Word) (a : Accumulator) :
    Eval unframe (9 * bits.length + 8)
      (state v p (Encoding.frame bits ++ rest) zero one a)
      (state false false (bits ++ rest) zero one a) := by
  simpa [unframe, Nat.add_assoc] using
    base_eval (SubexpKernelControl.unframe_eval v p bits rest zero one a)

theorem emitFramedLiteral_eval (v p : Bool) (bits rest zero one : Word) (a : Accumulator) :
    Eval emitFramedLiteral (7 * bits.length + 8)
      (state v p (Encoding.frame bits ++ rest) zero one a)
      (state false true rest zero one (emit (pushWord bits) a)) := by
  simpa [emitFramedLiteral, Nat.add_assoc] using
    base_eval (SubexpKernelControl.emitFramedLiteral_eval v p bits rest zero one a)

theorem emitLiteral_eval (which v p : Bool) (input zero one : Word) (a : Accumulator) :
    Eval (emitLiteral which) (8 * (if which then one else zero).length + 10)
      (state v p input zero one a)
      (state false false input zero one (emit (pushWord (if which then one else zero)) a)) := by
  simpa [emitLiteral, Nat.add_assoc] using
    base_eval (SubexpKernelControl.emitLiteral_eval which v p input zero one a)

theorem emitOperator_eval (mul v p : Bool) (input zero one : Word) (a : Accumulator) :
    Eval (emitOperator mul) ((if mul then 2 else 3) + 1)
      (state v p input zero one a)
      (state (if mul then v else false) p input zero one (emit (operator mul) a)) :=
  base_eval (SubexpKernelControl.emitOperator_eval mul v p input zero one a)

theorem countOne_eval (i : Fin 3) (v p : Bool) (input zero one : Word) (a : Accumulator) :
    Eval (countOne i) 2 (state v p input zero one a)
      (state v p input zero one (bump i a)) :=
  base_eval (SubexpKernelControl.countOne_eval i v p input zero one a)

theorem drain_eval (i : Fin 3) (mul : Bool) (word : Word) (v p : Bool)
    (input zero one : Word) (a : Accumulator) :
    Eval (drain i mul) ((if mul then 4 else 5) * word.length + 3)
      (state v p input zero one (setCounter i word a))
      (state false false input zero one (emit (operators mul word.length) (setCounter i [] a))) := by
  simpa [drain, Nat.add_assoc] using
    base_eval (SubexpKernelControl.drain_eval i mul word v p input zero one a)

end SubexponentialSAT.SubexpTableSource

end OAI.Algorithms

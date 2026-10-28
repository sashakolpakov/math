import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpAlgorithm
import OAI.Algorithms.SubexponentialSAT.SubexpPostfixControl
import OAI.Algorithms.SubexponentialSAT.SubexpHornerProgram
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.ExecCNFRecords

namespace OAI.Algorithms

/-!
# A fixed controller constructing the separated postfix source

The input contains literal payloads and the three nested lists of blocks,
color groups, and terms.  The controller only parses frames, copies bits,
and emits postfix tags.  It has no arithmetic callback and never builds a
Cartesian product of the inner lists.  Three unary stacks hold the pending
right-fold operators, so the emitted source has exactly the association of
`SubexpAlgorithm.momentExpression`.
-/

namespace SubexponentialSAT.SubexpKernelControl

open BitProgram StructuredCalls

abbrev Word := List Bool

def pushWord (payload : Word) : Word := false :: Encoding.frame payload

def operator (mul : Bool) : Word := [true, mul]

def operators (mul : Bool) (n : ℕ) : Word := (List.replicate n (operator mul)).flatten

structure Term where
  weight : Word
  factorCode : Word

structure Block where
  outside : Word
  groups : List (List Term)

def encodeTerm (t : Term) : Word := Encoding.encodeList id [t.weight, t.factorCode]
def encodeGroup (ts : List Term) : Word := Encoding.encodeList encodeTerm ts
def encodeBlock (b : Block) : Word :=
  Encoding.encodeList id [b.outside, Encoding.encodeList encodeGroup b.groups]
def encodeBlocks (bs : List Block) : Word := Encoding.encodeList encodeBlock bs

def termCode (t : Term) : Word := pushWord t.weight ++ t.factorCode ++ operator true

def groupCode (zero : Word) (ts : List Term) : Word :=
  (ts.map termCode).flatten ++ pushWord zero ++ operators false ts.length

def productCode (zero one : Word) (groups : List (List Term)) : Word :=
  (groups.map (groupCode zero)).flatten ++ pushWord one ++ operators true groups.length

def blockCode (zero one : Word) (b : Block) : Word :=
  pushWord b.outside ++ productCode zero one b.groups ++ operator true

def momentCode (zero one : Word) (bs : List Block) : Word :=
  (bs.map (blockCode zero one)).flatten ++ pushWord zero ++ operators false bs.length

def encodeInput (zero one : Word) (bs : List Block) : Word :=
  Encoding.encodeList id [zero, one, encodeBlocks bs]

def ofTerm {R : Type*} (encode : R → Word) (t : Algorithm.WeightedTerm R) : Term :=
  ⟨encode t.weight, SubexpPostfixControl.serializeCode encode t.group.compile⟩

def ofBlock {R : Type*} (encode : R → Word) (b : SubexpAlgorithm.Block R) : Block :=
  ⟨encode b.outside, b.groups.map (fun ts => ts.map (ofTerm encode))⟩

theorem serializeCode_append {R : Type*} (encode : R → Word)
    (a b : List (Algorithm.Instr R)) :
    SubexpPostfixControl.serializeCode encode (a ++ b) =
      SubexpPostfixControl.serializeCode encode a ++
        SubexpPostfixControl.serializeCode encode b := by
  induction a with
  | nil => rfl
  | cons a as ih => simp [SubexpPostfixControl.serializeCode, ih, List.append_assoc]

@[simp] theorem operators_zero (mul : Bool) : operators mul 0 = [] := rfl

theorem operators_succ (mul : Bool) (n : ℕ) :
    operators mul (n + 1) = operators mul n ++ operator mul := by
  simp [operators, List.replicate_succ', List.flatten_append]

theorem compile_sum {R : Type*} [Zero R] (encode : R → Word) (es : List (Algorithm.Expr R)) :
    SubexpPostfixControl.serializeCode encode (Algorithm.Expr.sum es).compile =
      (es.map (fun e => SubexpPostfixControl.serializeCode encode e.compile)).flatten ++
        pushWord (encode 0) ++ operators false es.length := by
  induction es with
  | nil => simp [Algorithm.Expr.sum, Algorithm.Expr.compile,
      SubexpPostfixControl.serializeCode, SubexpPostfixControl.serializeInstr, pushWord]
  | cons e es ih =>
      simp [Algorithm.Expr.sum, Algorithm.Expr.compile, serializeCode_append, ih,
        SubexpPostfixControl.serializeCode, SubexpPostfixControl.serializeInstr,
        operators_succ, operator, List.append_assoc]

theorem compile_product {R : Type*} [One R] (encode : R → Word) (es : List (Algorithm.Expr R)) :
    SubexpPostfixControl.serializeCode encode (Algorithm.Expr.product es).compile =
      (es.map (fun e => SubexpPostfixControl.serializeCode encode e.compile)).flatten ++
        pushWord (encode 1) ++ operators true es.length := by
  induction es with
  | nil => simp [Algorithm.Expr.product, Algorithm.Expr.compile,
      SubexpPostfixControl.serializeCode, SubexpPostfixControl.serializeInstr, pushWord]
  | cons e es ih =>
      simp [Algorithm.Expr.product, Algorithm.Expr.compile, serializeCode_append, ih,
        SubexpPostfixControl.serializeCode, SubexpPostfixControl.serializeInstr,
        operators_succ, operator, List.append_assoc]

theorem termCode_eq {R : Type*} (encode : R → Word) (t : Algorithm.WeightedTerm R) :
    termCode (ofTerm encode t) =
      SubexpPostfixControl.serializeCode encode t.expression.compile := by
  simp [termCode, ofTerm, Algorithm.WeightedTerm.expression, Algorithm.Expr.compile,
    serializeCode_append, SubexpPostfixControl.serializeCode,
    SubexpPostfixControl.serializeInstr, pushWord, operator]

theorem groupCode_eq {R : Type*} [Zero R] (encode : R → Word)
    (ts : List (Algorithm.WeightedTerm R)) :
    groupCode (encode 0) (ts.map (ofTerm encode)) =
      SubexpPostfixControl.serializeCode encode (SubexpAlgorithm.groupExpression ts).compile := by
  simp [SubexpAlgorithm.groupExpression, compile_sum, groupCode, List.map_map,
    Function.comp_def, termCode_eq]

theorem blockCode_eq {R : Type*} [Zero R] [One R] (encode : R → Word)
    (b : SubexpAlgorithm.Block R) :
    blockCode (encode 0) (encode 1) (ofBlock encode b) =
      SubexpPostfixControl.serializeCode encode b.expression.compile := by
  simp [blockCode, productCode, ofBlock, SubexpAlgorithm.Block.expression,
    Algorithm.Expr.compile, serializeCode_append, SubexpPostfixControl.serializeCode,
    SubexpPostfixControl.serializeInstr, compile_product, pushWord, operator,
    List.map_map, Function.comp_def, groupCode_eq]

theorem momentCode_eq {R : Type*} [Zero R] [One R] (encode : R → Word)
    (bs : List (SubexpAlgorithm.Block R)) :
    momentCode (encode 0) (encode 1) (bs.map (ofBlock encode)) =
      SubexpPostfixControl.serializeCode encode (SubexpAlgorithm.momentExpression bs).compile := by
  simp [momentCode, SubexpAlgorithm.momentExpression, compile_sum, List.map_map,
    Function.comp_def, blockCode_eq]

/-! ## Fixed source-constructor control -/

private abbrev atom (a : StructuredProgram.Atom 3 8) : Cmd 3 8 := .base (.atom a)
local infixr:60 " ;; " => Cmd.seq

private def registerMap (i : Fin 2) : Fin 3 := Fin.castAdd 1 i
private def pairMap (a b : Fin 8) (i : Fin 2) : Fin 8 := if i = 0 then a else b
private def tripleMap (a b c : Fin 8) (i : Fin 3) : Fin 8 :=
  if i = 0 then a else if i = 1 then b else c

/-- Every list length is data on stack 0. -/
abbrev popTag : Cmd 3 8 := atom (.pop 0 0 1)

abbrev unframe : Cmd 3 8 :=
  .call (ProgramLinking.liftProgram ParserProgram.unframeProgram registerMap (pairMap 0 4))

/-- Copy an already-framed literal without changing its coefficient encoding. -/
abbrev captureFrame : Cmd 3 8 :=
  .call (ProgramLinking.liftProgram
    { ExecCNFRecords.captureProgram with entry := 4 } registerMap (tripleMap 0 4 3))

abbrev emitFramedLiteral : Cmd 3 8 := atom (.set 0 false) ;; atom (.push 3 0) ;; captureFrame

/-- The factor expression was constructed by the factor source compiler. -/
abbrev appendPayload : Cmd 3 8 :=
  .call (ProgramLinking.liftProgram ParserProgram.frameProgram registerMap (pairMap 0 3))

abbrev emitLiteral (source : Fin 8) : Cmd 3 8 :=
  .call (ProgramLinking.liftProgram SubexpHornerProgram.Literal.program id
    (tripleMap source 3 4))

abbrev emitOperator (mul : Bool) : Cmd 3 8 :=
  if mul then atom (.push 3 2) ;; atom (.push 3 2)
  else atom (.push 3 2) ;; atom (.set 0 false) ;; atom (.push 3 0)

abbrev countOne (counter : Fin 8) : Cmd 3 8 := atom (.push counter 2)

abbrev drain (counter : Fin 8) (mul : Bool) : Cmd 3 8 :=
  atom (.pop counter 0 1) ;;
    .while 1 (emitOperator mul ;; atom (.pop counter 0 1))

/-- The fixed body consumes exactly one unframed payload, then the next marker
is read. The same control table handles every list length. -/
abbrev scanLoop (body : Cmd 3 8) : Cmd 3 8 := .while 0 (unframe ;; body ;; popTag)

abbrev scan (body : Cmd 3 8) : Cmd 3 8 := popTag ;; scanLoop body

abbrev termBody : Cmd 3 8 :=
  popTag ;; emitFramedLiteral ;; popTag ;; appendPayload ;; popTag ;;
    emitOperator true ;; countOne 7

abbrev groupBody : Cmd 3 8 :=
  scan termBody ;; emitLiteral 1 ;; drain 7 false ;; countOne 6

abbrev blockBody : Cmd 3 8 :=
  popTag ;; emitFramedLiteral ;; popTag ;; unframe ;; scan groupBody ;;
    emitLiteral 2 ;; drain 6 true ;; popTag ;; emitOperator true ;; countOne 5

abbrev kernel : Cmd 3 8 := scan blockBody ;; emitLiteral 1 ;; drain 5 false

/-- A concrete finite instruction table; no arithmetic or traversal service
is passed as an argument to the constructor. -/
abbrev kernelProgram : Program 3 8 (StructuredCalls.size kernel + 1) :=
  StructuredCalls.compiled kernel 0 3

/-! ## Concrete machine states and elementary traces -/

structure Accumulator where
  output : Word
  outer : Word
  groups : Word
  terms : Word

def state (v p : Bool) (source zero one : Word) (a : Accumulator) : State 3 8 :=
  ⟨SubexpHornerProgram.triple v p true,
    ![source, zero, one, a.output, [], a.outer, a.groups, a.terms]⟩

def emit (code : Word) (a : Accumulator) : Accumulator :=
  { a with output := code.reverse ++ a.output }

@[simp] theorem emit_nil (a : Accumulator) : emit [] a = a := by cases a; rfl

theorem emit_emit (x y : Word) (a : Accumulator) : emit y (emit x a) = emit (x ++ y) a := by
  cases a
  simp [emit, List.reverse_append, List.append_assoc]

private theorem state_ext {v p v' p' : Bool} {source zero one source' zero' one' : Word}
    {a a' : Accumulator} (hv : v = v') (hp : p = p') (hs : source = source')
    (hz : zero = zero') (ho : one = one') (ha : a = a') :
    state v p source zero one a = state v' p' source' zero' one' a' := by
  subst_vars
  rfl

theorem popTag_eval (b v p : Bool) (source zero one : Word) (a : Accumulator) :
    Eval popTag 1 (state v p (b :: source) zero one a)
      (state b true source zero one a) := by
  have h : (StructuredProgram.Atom.pop (0 : Fin 8) (0 : Fin 3) 1).eval
      (state v p (b :: source) zero one a) = state b true source zero one a := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ StructuredProgram.Atom.instr,
        execInstr, readRegs, state, SubexpHornerProgram.triple]
    · funext i
      fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr, state]
  rw [← h]
  exact .base (.atom _ _)

theorem setValue_eval (b v p : Bool) (source zero one : Word) (a : Accumulator) :
    Eval (atom (.set 0 b)) 1 (state v p source zero one a)
      (state b p source zero one a) := by
  have h : (StructuredProgram.Atom.set (s := 8) (0 : Fin 3) b).eval
      (state v p source zero one a) = state b p source zero one a := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ StructuredProgram.Atom.instr,
        execInstr, state, SubexpHornerProgram.triple]
    · rfl
  rw [← h]
  exact .base (.atom _ _)

theorem pushValue_eval (v p : Bool) (source zero one : Word) (a : Accumulator) :
    Eval (atom (.push 3 0)) 1 (state v p source zero one a)
      (state v p source zero one { a with output := v :: a.output }) := by
  have h : (StructuredProgram.Atom.push (3 : Fin 8) (0 : Fin 3)).eval
      (state v p source zero one a) =
      state v p source zero one { a with output := v :: a.output } := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [ StructuredProgram.Atom.instr,
        execInstr, state, SubexpHornerProgram.triple]
  rw [← h]
  exact .base (.atom _ _)

theorem pushTrue_eval (v p : Bool) (source zero one : Word) (a : Accumulator) :
    Eval (atom (.push 3 2)) 1 (state v p source zero one a)
      (state v p source zero one { a with output := true :: a.output }) := by
  have h : (StructuredProgram.Atom.push (3 : Fin 8) (2 : Fin 3)).eval
      (state v p source zero one a) =
      state v p source zero one { a with output := true :: a.output } := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [ StructuredProgram.Atom.instr,
        execInstr, state, SubexpHornerProgram.triple]
  rw [← h]
  exact .base (.atom _ _)

theorem emitOperator_eval (mul v p : Bool) (source zero one : Word) (a : Accumulator) :
    Eval (emitOperator mul) (if mul then 2 else 3)
      (state v p source zero one a)
      (state (if mul then v else false) p source zero one (emit (operator mul) a)) := by
  cases mul
  · simpa [emitOperator, emit, operator] using
      Eval.seq (pushTrue_eval v p source zero one a)
        (Eval.seq (setValue_eval false v p source zero one { a with output := true :: a.output })
          (pushValue_eval false p source zero one { a with output := true :: a.output }))
  · simpa [emitOperator, emit, operator] using
      Eval.seq (pushTrue_eval v p source zero one a)
        (pushTrue_eval v p source zero one { a with output := true :: a.output })

private theorem extend_pair {α β : Type} [DecidableEq α] (x y : α) (hxy : x ≠ y)
    (a b : β) (base : α → β) :
    Function.extend (ParserProgram.pair x y) (ParserProgram.pair a b) base =
      Function.update (Function.update base x a) y b := by
  classical
  have hinj : Function.Injective (ParserProgram.pair x y) := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [ParserProgram.pair, Ne.symm hxy]
  funext z
  by_cases hx : z = x
  · subst z
    have h := hinj.extend_apply (ParserProgram.pair a b) base (0 : Fin 2)
    simpa [ParserProgram.pair, hxy] using h
  · by_cases hy : z = y
    · subst z
      have h := hinj.extend_apply (ParserProgram.pair a b) base (1 : Fin 2)
      simpa [ParserProgram.pair] using h
    · have hout : ¬ ∃ i, ParserProgram.pair x y i = z := by
        rintro ⟨i, hi⟩
        fin_cases i <;> simp [ParserProgram.pair] at hi <;> subst z <;> contradiction
      rw [Function.extend_apply' _ _ _ hout]
      simp [hx, hy]

private theorem extend_triple {α β : Type} [DecidableEq α] (x y z : α)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (a b c : β) (base : α → β) :
    Function.extend (SubexpHornerProgram.triple x y z)
        (SubexpHornerProgram.triple a b c) base =
      Function.update (Function.update (Function.update base x a) y b) z c := by
  classical
  have hinj : Function.Injective (SubexpHornerProgram.triple x y z) := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [SubexpHornerProgram.triple,
        Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]
  funext w
  by_cases hwx : w = x
  · subst w
    have h := hinj.extend_apply (SubexpHornerProgram.triple a b c) base (0 : Fin 3)
    simpa [SubexpHornerProgram.triple, hxy, hxz] using h
  · by_cases hwy : w = y
    · subst w
      have h := hinj.extend_apply (SubexpHornerProgram.triple a b c) base (1 : Fin 3)
      simpa [SubexpHornerProgram.triple, hyz] using h
    · by_cases hwz : w = z
      · subst w
        have h := hinj.extend_apply (SubexpHornerProgram.triple a b c) base (2 : Fin 3)
        simpa [SubexpHornerProgram.triple] using h
      · have hout : ¬ ∃ i, SubexpHornerProgram.triple x y z i = w := by
          rintro ⟨i, hi⟩
          fin_cases i <;> simp [SubexpHornerProgram.triple] at hi <;>
            subst w <;> contradiction
        rw [Function.extend_apply' _ _ _ hout]
        simp [hwx, hwy, hwz]

private theorem registerMap_eq : registerMap = ParserProgram.pair (0 : Fin 3) 1 := by
  funext i
  fin_cases i <;> rfl

private def parserState (v p : Bool) (src dst : Word) : State 2 2 :=
  ⟨ParserProgram.pair v p, ParserProgram.pair src dst⟩

private theorem embed_parser_scratch (v p v' p' : Bool) (src src' zero one : Word)
    (a : Accumulator) :
    embedState registerMap (pairMap 0 4) (state v p src zero one a)
      (parserState v' p' src' []) = state v' p' src' zero one a := by
  unfold embedState parserState
  rw [registerMap_eq]
  change StructuredProgram.State.mk
    (Function.extend (ParserProgram.pair 0 1) (ParserProgram.pair v' p') _)
    (Function.extend (ParserProgram.pair 0 4) (ParserProgram.pair src' []) _) = _
  rw [extend_pair _ _ (by decide), extend_pair _ _ (by decide)]
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i <;> simp [state, SubexpHornerProgram.triple]
  · funext i
    fin_cases i <;> simp [state]

private theorem embed_parser_output (v p v' p' : Bool) (src src' zero one out : Word)
    (a : Accumulator) :
    embedState registerMap (pairMap 0 3) (state v p src zero one a)
      (parserState v' p' src' out) = state v' p' src' zero one { a with output := out } := by
  unfold embedState parserState
  rw [registerMap_eq]
  change StructuredProgram.State.mk
    (Function.extend (ParserProgram.pair 0 1) (ParserProgram.pair v' p') _)
    (Function.extend (ParserProgram.pair 0 3) (ParserProgram.pair src' out) _) = _
  rw [extend_pair _ _ (by decide), extend_pair _ _ (by decide)]
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i <;> simp [state, SubexpHornerProgram.triple]
  · funext i
    fin_cases i <;> simp [state]

theorem unframe_eval (v p : Bool) (bits rest zero one : Word) (a : Accumulator) :
    Eval unframe (9 * bits.length + 7)
      (state v p (Encoding.frame bits ++ rest) zero one a)
      (state false false (bits ++ rest) zero one a) := by
  have h := eval_call_lifted ParserProgram.unframeProgram registerMap (pairMap 0 4)
    (state v p (Encoding.frame bits ++ rest) zero one a)
    (by decide) (by decide)
    (a := parserState v p (Encoding.frame bits ++ rest) [])
    (b := parserState false false (bits ++ rest) [])
    (ParserProgram.unframe_trace bits rest v p)
  simpa only [unframe, embed_parser_scratch] using h

theorem appendPayload_eval (v p : Bool) (bits rest zero one : Word) (a : Accumulator) :
    Eval appendPayload (6 * bits.length + 4)
      (state v p (Encoding.frame bits ++ rest) zero one a)
      (state false true rest zero one (emit bits a)) := by
  have h := eval_call_lifted ParserProgram.frameProgram registerMap (pairMap 0 3)
    (state v p (Encoding.frame bits ++ rest) zero one a)
    (by decide) (by decide)
    (a := parserState v p (Encoding.frame bits ++ rest) a.output)
    (b := parserState false true rest (bits.reverse ++ a.output))
    (ParserProgram.frame_trace bits rest a.output v p)
  simpa only [appendPayload, embed_parser_output, emit] using h

private def captureState (v p : Bool) (src out : Word) : State 2 3 :=
  ⟨ParserProgram.pair v p, SubexpHornerProgram.triple src [] out⟩

private theorem embed_capture (v p v' p' : Bool) (src src' zero one out : Word)
    (a : Accumulator) :
    embedState registerMap (tripleMap 0 4 3) (state v p src zero one a)
      (captureState v' p' src' out) = state v' p' src' zero one { a with output := out } := by
  unfold embedState captureState
  rw [registerMap_eq]
  change StructuredProgram.State.mk
    (Function.extend (ParserProgram.pair 0 1) (ParserProgram.pair v' p') _)
    (Function.extend (SubexpHornerProgram.triple 0 4 3)
      (SubexpHornerProgram.triple src' [] out) _) = _
  rw [extend_pair _ _ (by decide),
    extend_triple _ _ _ (by decide) (by decide) (by decide)]
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i <;> simp [state, SubexpHornerProgram.triple]
  · funext i
    fin_cases i <;> simp [state]

theorem captureFrame_eval (v p : Bool) (bits rest zero one : Word) (a : Accumulator) :
    Eval captureFrame (7 * bits.length + 5)
      (state v p (Encoding.frame bits ++ rest) zero one a)
      (state false true rest zero one (emit (Encoding.frame bits) a)) := by
  have h := eval_call_lifted { ExecCNFRecords.captureProgram with entry := 4 }
    registerMap (tripleMap 0 4 3)
    (state v p (Encoding.frame bits ++ rest) zero one a)
    (by decide) (by decide)
    (a := captureState v p (Encoding.frame bits ++ rest) a.output)
    (b := captureState false true rest ((Encoding.frame bits).reverse ++ a.output))
    (ExecCNFRecords.capture_frame_trace bits rest [] a.output v p)
  simpa only [captureFrame, embed_capture, emit] using h

theorem emitFramedLiteral_eval (v p : Bool) (bits rest zero one : Word) (a : Accumulator) :
    Eval emitFramedLiteral (7 * bits.length + 7)
      (state v p (Encoding.frame bits ++ rest) zero one a)
      (state false true rest zero one (emit (pushWord bits) a)) := by
  have hs := setValue_eval false v p (Encoding.frame bits ++ rest) zero one a
  have hp := pushValue_eval false p (Encoding.frame bits ++ rest) zero one a
  have hc := captureFrame_eval false p bits rest zero one { a with output := false :: a.output }
  convert Eval.seq hs (Eval.seq hp hc) using 1 <;>
    simp [ emit, pushWord, List.reverse_cons, List.append_assoc, Nat.add_comm ] ; omega

private theorem extend_id {α β : Type*} (f base : α → β) : Function.extend id f base = f := by
  funext x
  exact Function.injective_id.extend_apply f base x

private def literalState (v p : Bool) (payload out : Word) : State 3 3 :=
  ⟨SubexpHornerProgram.triple v p true, SubexpHornerProgram.triple payload out []⟩

private theorem embed_literal (which v p v' p' : Bool) (src zero one out : Word)
    (a : Accumulator) :
    embedState id (tripleMap (if which then 2 else 1) 3 4) (state v p src zero one a)
      (literalState v' p' (if which then one else zero) out) =
      state v' p' src zero one { a with output := out } := by
  unfold embedState literalState
  rw [extend_id]
  change StructuredProgram.State.mk _
    (Function.extend (SubexpHornerProgram.triple (if which then 2 else 1) 3 4)
      (SubexpHornerProgram.triple (if which then one else zero) out []) _) = _
  rw [extend_triple _ _ _ (by cases which <;> decide)
    (by cases which <;> decide) (by decide)]
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    cases which <;> fin_cases i <;> simp [state]

theorem emitLiteral_eval (which v p : Bool) (src zero one : Word) (a : Accumulator) :
    Eval (emitLiteral (if which then 2 else 1))
      (8 * (if which then one else zero).length + 9)
      (state v p src zero one a)
      (state false false src zero one (emit (pushWord (if which then one else zero)) a)) := by
  have h := eval_call_lifted SubexpHornerProgram.Literal.program id
    (tripleMap (if which then 2 else 1) 3 4) (state v p src zero one a)
    Function.injective_id (by cases which <;> decide)
    (a := literalState v p (if which then one else zero) a.output)
    (b := literalState false false (if which then one else zero)
      ((pushWord (if which then one else zero)).reverse ++ a.output))
    (SubexpHornerProgram.Literal.trace (if which then one else zero) a.output v p true)
  simpa only [emitLiteral, embed_literal, emit] using h

def counterPort (i : Fin 3) : Fin 8 := if i = 0 then 5 else if i = 1 then 6 else 7

def counterWord (i : Fin 3) (a : Accumulator) : Word :=
  if i = 0 then a.outer else if i = 1 then a.groups else a.terms

def setCounter (i : Fin 3) (word : Word) (a : Accumulator) : Accumulator :=
  if i = 0 then { a with outer := word }
  else if i = 1 then { a with groups := word }
  else { a with terms := word }

@[simp] theorem counterWord_setCounter (i : Fin 3) (word : Word) (a : Accumulator) :
    counterWord i (setCounter i word a) = word := by
  fin_cases i <;> simp [counterWord, setCounter]

@[simp] theorem setCounter_same (i : Fin 3) (a : Accumulator) :
    setCounter i (counterWord i a) a = a := by
  fin_cases i <;> cases a <;> rfl

@[simp] theorem setCounter_setCounter (i : Fin 3) (x y : Word) (a : Accumulator) :
    setCounter i x (setCounter i y a) = setCounter i x a := by
  fin_cases i <;> rfl

@[simp] theorem setCounter_emit (i : Fin 3) (word code : Word) (a : Accumulator) :
    setCounter i word (emit code a) = emit code (setCounter i word a) := by
  fin_cases i <;> rfl

theorem countOne_eval (i : Fin 3) (v p : Bool) (src zero one : Word) (a : Accumulator) :
    Eval (countOne (counterPort i)) 1 (state v p src zero one a)
      (state v p src zero one (setCounter i (true :: counterWord i a) a)) := by
  have h : (StructuredProgram.Atom.push (counterPort i) (2 : Fin 3)).eval
      (state v p src zero one a) =
      state v p src zero one (setCounter i (true :: counterWord i a) a) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases i <;> fin_cases j <;>
        simp [ StructuredProgram.Atom.instr,
          execInstr, state, SubexpHornerProgram.triple, counterPort, counterWord, setCounter]
  rw [← h]
  exact .base (.atom _ _)

def afterCounter (i : Fin 3) (word src zero one : Word) (a : Accumulator) : State 3 8 :=
  state (word.head?.getD false) word.head?.isSome src zero one (setCounter i word.tail a)

theorem popCounter_eval (i : Fin 3) (word : Word) (v p : Bool)
    (src zero one : Word) (a : Accumulator) :
    Eval (atom (.pop (counterPort i) 0 1)) 1
      (state v p src zero one (setCounter i word a))
      (afterCounter i word src zero one a) := by
  have h : (StructuredProgram.Atom.pop (counterPort i) (0 : Fin 3) 1).eval
      (state v p src zero one (setCounter i word a)) =
      afterCounter i word src zero one a := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      cases word <;> fin_cases i <;> fin_cases j <;>
        simp [ StructuredProgram.Atom.instr,
          execInstr, readRegs, state, SubexpHornerProgram.triple,
          counterPort, setCounter]
    · funext j
      cases word <;> fin_cases i <;> fin_cases j <;>
        simp [ StructuredProgram.Atom.instr,
          execInstr, state, counterPort, setCounter]
  rw [← h]
  exact .base (.atom _ _)

theorem operators_cons (mul : Bool) (n : ℕ) :
    operator mul ++ operators mul n = operators mul (n + 1) := by
  simp [operators, List.replicate_succ, List.flatten_cons]

theorem drainLoop_eval (i : Fin 3) (mul : Bool) (word src zero one : Word) (a : Accumulator) :
    Eval (.while 1 (emitOperator mul ;; atom (.pop (counterPort i) 0 1)))
      ((if mul then 4 else 5) * word.length + 1)
      (afterCounter i word src zero one a)
      (state false false src zero one (emit (operators mul word.length) (setCounter i [] a))) := by
  induction word generalizing a with
  | nil =>
      simpa [afterCounter] using
        (Eval.while_false (test := (1 : Fin 3))
          (body := emitOperator mul ;; atom (.pop (counterPort i) 0 1))
          (a := state false false src zero one (setCounter i [] a)) (by rfl))
  | cons b bs ih =>
      have hop := emitOperator_eval mul b true src zero one (setCounter i bs a)
      have hpop := popCounter_eval i bs (if mul then b else false) true src zero one
        (emit (operator mul) a)
      rw [setCounter_emit] at hpop
      have hrest := ih (emit (operator mul) a)
      have hguard : (afterCounter i (b :: bs) src zero one a).regs 1 = true := by rfl
      have h := Eval.while_true hguard (Eval.seq hop hpop) hrest
      rw [setCounter_emit, emit_emit, operators_cons] at h
      cases mul <;> convert h using 1 <;>
        simp [ Nat.mul_add, Nat.add_left_comm, Nat.add_comm] <;> omega

theorem drain_eval (i : Fin 3) (mul : Bool) (word : Word) (v p : Bool)
    (src zero one : Word) (a : Accumulator) :
    Eval (drain (counterPort i) mul) ((if mul then 4 else 5) * word.length + 2)
      (state v p src zero one (setCounter i word a))
      (state false false src zero one (emit (operators mul word.length) (setCounter i [] a))) := by
  have h := Eval.seq (popCounter_eval i word v p src zero one a)
    (drainLoop_eval i mul word src zero one a)
  cases mul <;> convert h using 1 <;>
    simp [ Nat.add_comm] <;> omega

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

def scanCost {α : Type*} (encode : α → Word) (cost : α → ℕ) (xs : List α) : ℕ :=
  (xs.map (fun x => 9 * (encode x).length + cost x + 9)).sum

def afterTag {α : Type*} (encode : α → Word) (xs : List α) (rest zero one : Word)
    (a : Accumulator) : State 3 8 :=
  match xs with
  | [] => state false true rest zero one a
  | x :: xs => state true true
      (Encoding.frame (encode x) ++ (Encoding.encodeList encode xs ++ rest)) zero one a

theorem popList_eval {α : Type*} (encode : α → Word) (xs : List α)
    (v p : Bool) (rest zero one : Word) (a : Accumulator) :
    Eval popTag 1 (state v p (Encoding.encodeList encode xs ++ rest) zero one a)
      (afterTag encode xs rest zero one a) := by
  cases xs with
  | nil => simpa [afterTag, Encoding.encodeList] using popTag_eval false v p rest zero one a
  | cons x xs =>
      simpa [afterTag, Encoding.encodeList, List.append_assoc] using
        popTag_eval true v p (Encoding.frame (encode x) ++
          (Encoding.encodeList encode xs ++ rest)) zero one a

theorem scanLoop_eval {α : Type*} (body : Cmd 3 8) (encode : α → Word)
    (cost : α → ℕ) (update : α → Accumulator → Accumulator)
    (invariant : Accumulator → Prop) (zero one : Word) (vb pb : Bool)
    (hbody : ∀ x rest a, invariant a →
      Eval body (cost x) (state false false (encode x ++ rest) zero one a)
        (state vb pb rest zero one (update x a)))
    (hpreserve : ∀ x a, invariant a → invariant (update x a))
    (xs : List α) (rest : Word) (a : Accumulator) (ha : invariant a) :
    Eval (scanLoop body) (1 + scanCost encode cost xs)
      (afterTag encode xs rest zero one a)
      (state false true rest zero one (xs.foldl (fun a x => update x a) a)) := by
  induction xs generalizing a with
  | nil =>
      apply Eval.while_false
      simp [afterTag, state, SubexpHornerProgram.triple]
  | cons x xs ih =>
      let tail := Encoding.encodeList encode xs ++ rest
      have hread := unframe_eval true true (encode x) tail zero one a
      have hrun := hbody x tail a ha
      have hpop := popList_eval encode xs vb pb rest zero one (update x a)
      have hrest := ih (update x a) (hpreserve x a ha)
      have hguard : (afterTag encode (x :: xs) rest zero one a).regs 0 = true := by
        simp [afterTag, state, SubexpHornerProgram.triple]
      have hstep := Eval.seq hread (Eval.seq hrun hpop)
      have h := Eval.while_true hguard hstep hrest
      convert h using 1 <;>
        simp [ scanCost, List.foldl_cons,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] ; omega

theorem scan_eval {α : Type*} (body : Cmd 3 8) (encode : α → Word)
    (cost : α → ℕ) (update : α → Accumulator → Accumulator)
    (invariant : Accumulator → Prop) (zero one : Word) (vb pb : Bool)
    (hbody : ∀ x rest a, invariant a →
      Eval body (cost x) (state false false (encode x ++ rest) zero one a)
        (state vb pb rest zero one (update x a)))
    (hpreserve : ∀ x a, invariant a → invariant (update x a))
    (xs : List α) (v p : Bool) (rest : Word) (a : Accumulator) (ha : invariant a) :
    Eval (scan body) (2 + scanCost encode cost xs)
      (state v p (Encoding.encodeList encode xs ++ rest) zero one a)
      (state false true rest zero one (xs.foldl (fun a x => update x a) a)) := by
  have hpop := popList_eval encode xs v p rest zero one a
  have hloop := scanLoop_eval body encode cost update invariant zero one vb pb
    hbody hpreserve xs rest a ha
  convert Eval.seq hpop hloop using 1 ; omega

@[simp] theorem counterWord_emit (i : Fin 3) (code : Word) (a : Accumulator) :
    counterWord i (emit code a) = counterWord i a := by
  fin_cases i <;> simp [counterWord, emit]

def bump (i : Fin 3) (a : Accumulator) : Accumulator :=
  setCounter i (true :: counterWord i a) a

def termUpdate (t : Term) (a : Accumulator) : Accumulator := bump 2 (emit (termCode t) a)
def groupUpdate (zero : Word) (ts : List Term) (a : Accumulator) : Accumulator :=
  bump 1 (emit (groupCode zero ts) a)
def blockUpdate (zero one : Word) (b : Block) (a : Accumulator) : Accumulator :=
  bump 0 (emit (blockCode zero one b) a)

def termCost (t : Term) : ℕ := 7 * t.weight.length + 6 * t.factorCode.length + 17

theorem termBody_eval (t : Term) (rest zero one : Word) (a : Accumulator) :
    Eval termBody (termCost t)
      (state false false (encodeTerm t ++ rest) zero one a)
      (state false true rest zero one (termUpdate t a)) := by
  let tail := true :: (Encoding.frame t.factorCode ++ (false :: rest))
  have h₁ := popTag_eval true false false (Encoding.frame t.weight ++ tail) zero one a
  have h₂ := emitFramedLiteral_eval true true t.weight tail zero one a
  have h₃ := popTag_eval true false true (Encoding.frame t.factorCode ++ (false :: rest))
    zero one (emit (pushWord t.weight) a)
  have h₄ := appendPayload_eval true true t.factorCode (false :: rest) zero one
    (emit (pushWord t.weight) a)
  have h₅ := popTag_eval false false true rest zero one
    (emit t.factorCode (emit (pushWord t.weight) a))
  have h₆ := emitOperator_eval true false true rest zero one
    (emit t.factorCode (emit (pushWord t.weight) a))
  have h₇ := countOne_eval 2 false true rest zero one
    (emit (operator true) (emit t.factorCode (emit (pushWord t.weight) a)))
  have h := Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ (Eval.seq h₄
    (Eval.seq h₅ (Eval.seq h₆ h₇)))))
  convert h using 1 <;>
    simp [termBody, termCost, encodeTerm, Encoding.encodeList, tail,
      termUpdate, bump, termCode, emit_emit, counterPort, List.append_assoc,
      Nat.add_assoc, Nat.add_comm ] ; omega

theorem fold_bump_emit {α : Type*} (i : Fin 3) (code : α → Word)
    (xs : List α) (a : Accumulator) :
    xs.foldl (fun a x => bump i (emit (code x) a)) a =
      emit ((xs.map code).flatten)
        (setCounter i (List.replicate xs.length true ++ counterWord i a) a) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      simp [bump, emit_emit, List.replicate_succ', List.append_assoc]

def groupCost (zero : Word) (ts : List Term) : ℕ :=
  scanCost encodeTerm termCost ts + 8 * zero.length + 5 * ts.length + 14

theorem groupBody_eval (ts : List Term) (rest zero one : Word) (a : Accumulator)
    (ha : a.terms = []) :
    Eval groupBody (groupCost zero ts)
      (state false false (encodeGroup ts ++ rest) zero one a)
      (state false false rest zero one (groupUpdate zero ts a)) := by
  let pre := (ts.map termCode).flatten
  let pending := List.replicate ts.length true
  have hs := scan_eval termBody encodeTerm termCost termUpdate (fun _ => True)
    zero one false true (fun t rest a _ => termBody_eval t rest zero one a)
    (fun _ _ _ => trivial) ts false false rest a trivial
  have hs' : Eval (scan termBody) (2 + scanCost encodeTerm termCost ts)
      (state false false (encodeGroup ts ++ rest) zero one a)
      (state false true rest zero one (emit pre (setCounter 2 pending a))) := by
    simpa [encodeGroup, termUpdate, fold_bump_emit, pre, pending, counterWord, ha] using hs
  have hz := emitLiteral_eval false false true rest zero one (emit pre (setCounter 2 pending a))
  have hd := drain_eval 2 false pending false false rest zero one (emit (pre ++ pushWord zero) a)
  have hd' : Eval (drain 7 false) (5 * ts.length + 2)
      (state false false rest zero one (emit (pushWord zero) (emit pre (setCounter 2 pending a))))
      (state false false rest zero one (emit (groupCode zero ts) a)) := by
    have hclear := setCounter_same (2 : Fin 3) a
    have hword : counterWord (2 : Fin 3) a = [] := ha
    rw [hword] at hclear
    simpa [counterPort, pending, groupCode, pre, emit_emit, hclear,
      List.append_assoc] using hd
  have hc := countOne_eval 1 false false rest zero one (emit (groupCode zero ts) a)
  have h := Eval.seq hs' (Eval.seq hz (Eval.seq hd' hc))
  convert h using 1 <;>
    simp [groupBody, groupCost, groupUpdate, bump, counterPort,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] ; omega

def blockCost (zero one : Word) (b : Block) : ℕ :=
  7 * b.outside.length + 9 * (Encoding.encodeList encodeGroup b.groups).length +
    scanCost encodeGroup (groupCost zero) b.groups + 8 * one.length +
      4 * b.groups.length + 33

theorem blockBody_eval (b : Block) (rest zero one : Word) (a : Accumulator)
    (hg : a.groups = []) (ht : a.terms = []) :
    Eval blockBody (blockCost zero one b)
      (state false false (encodeBlock b ++ rest) zero one a)
      (state false true rest zero one (blockUpdate zero one b a)) := by
  let groups := Encoding.encodeList encodeGroup b.groups
  let tail := true :: (Encoding.frame groups ++ (false :: rest))
  let a₀ := emit (pushWord b.outside) a
  let pre := (b.groups.map (groupCode zero)).flatten
  let pending := List.replicate b.groups.length true
  have h₁ := popTag_eval true false false (Encoding.frame b.outside ++ tail) zero one a
  have h₂ := emitFramedLiteral_eval true true b.outside tail zero one a
  have h₃ := popTag_eval true false true (Encoding.frame groups ++ (false :: rest)) zero one a₀
  have h₄ := unframe_eval true true groups (false :: rest) zero one a₀
  have ha₀g : a₀.groups = [] := hg
  have ha₀t : a₀.terms = [] := ht
  have hs := scan_eval groupBody encodeGroup (groupCost zero) (groupUpdate zero)
    (fun a => a.terms = []) zero one false false
    (fun ts rest a ha => groupBody_eval ts rest zero one a ha)
    (by intro ts a ha; simpa [groupUpdate, bump, setCounter, emit] using ha)
    b.groups false false (false :: rest) a₀ ha₀t
  have hs' : Eval (scan groupBody) (2 + scanCost encodeGroup (groupCost zero) b.groups)
      (state false false (groups ++ (false :: rest)) zero one a₀)
      (state false true (false :: rest) zero one (emit pre (setCounter 1 pending a₀))) := by
    simpa [groups, groupUpdate, fold_bump_emit, pre, pending, counterWord, ha₀g] using hs
  have hz := emitLiteral_eval true false true (false :: rest) zero one
    (emit pre (setCounter 1 pending a₀))
  have hd := drain_eval 1 true pending false false (false :: rest) zero one
    (emit (pre ++ pushWord one) a₀)
  have hd' : Eval (drain 6 true) (4 * b.groups.length + 2)
      (state false false (false :: rest) zero one
        (emit (pushWord one) (emit pre (setCounter 1 pending a₀))))
      (state false false (false :: rest) zero one (emit (productCode zero one b.groups) a₀)) := by
    have hclear := setCounter_same (1 : Fin 3) a₀
    have hword : counterWord (1 : Fin 3) a₀ = [] := ha₀g
    rw [hword] at hclear
    simpa [counterPort, pending, productCode, pre, emit_emit, hclear,
      List.append_assoc] using hd
  have h₅ := popTag_eval false false false rest zero one
    (emit (productCode zero one b.groups) a₀)
  have h₆ := emitOperator_eval true false true rest zero one
    (emit (productCode zero one b.groups) a₀)
  have h₇ := countOne_eval 0 false true rest zero one
    (emit (operator true) (emit (productCode zero one b.groups) a₀))
  have h := Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ (Eval.seq h₄ (Eval.seq hs'
    (Eval.seq hz (Eval.seq hd' (Eval.seq h₅ (Eval.seq h₆ h₇))))))))
  convert h using 1 <;>
    simp [blockBody, blockCost, encodeBlock, Encoding.encodeList, tail, groups,
      blockUpdate, blockCode, bump, a₀, emit_emit, counterPort, List.append_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] ; omega

def kernelCost (zero one : Word) (bs : List Block) : ℕ :=
  scanCost encodeBlock (blockCost zero one) bs + 8 * zero.length + 5 * bs.length + 13

/-- Exact execution of the complete three-level source constructor. All
service bodies are the concrete parser, literal emitter, and bit instructions
appearing in `kernel`; no callback correctness is supplied by this theorem. -/
theorem kernel_eval (bs : List Block) (v p : Bool) (rest zero one : Word) (a : Accumulator)
    (ho : a.outer = []) (hg : a.groups = []) (ht : a.terms = []) :
    Eval kernel (kernelCost zero one bs)
      (state v p (encodeBlocks bs ++ rest) zero one a)
      (state false false rest zero one (emit (momentCode zero one bs) a)) := by
  let pre := (bs.map (blockCode zero one)).flatten
  let pending := List.replicate bs.length true
  have hs := scan_eval blockBody encodeBlock (blockCost zero one) (blockUpdate zero one)
    (fun a => a.groups = [] ∧ a.terms = []) zero one false true
    (fun b rest a ha => blockBody_eval b rest zero one a ha.1 ha.2)
    (by intro b a ha; simpa [blockUpdate, bump, setCounter, emit] using ha)
    bs v p rest a ⟨hg, ht⟩
  have hs' : Eval (scan blockBody) (2 + scanCost encodeBlock (blockCost zero one) bs)
      (state v p (encodeBlocks bs ++ rest) zero one a)
      (state false true rest zero one (emit pre (setCounter 0 pending a))) := by
    simpa [encodeBlocks, blockUpdate, fold_bump_emit, pre, pending, counterWord, ho] using hs
  have hz := emitLiteral_eval false false true rest zero one (emit pre (setCounter 0 pending a))
  have hd := drain_eval 0 false pending false false rest zero one (emit (pre ++ pushWord zero) a)
  have hd' : Eval (drain 5 false) (5 * bs.length + 2)
      (state false false rest zero one (emit (pushWord zero) (emit pre (setCounter 0 pending a))))
      (state false false rest zero one (emit (momentCode zero one bs) a)) := by
    have hclear := setCounter_same (0 : Fin 3) a
    have hword : counterWord (0 : Fin 3) a = [] := ho
    rw [hword] at hclear
    simpa [counterPort, pending, momentCode, pre, emit_emit, hclear,
      List.append_assoc] using hd
  convert Eval.seq hs' (Eval.seq hz hd') using 1 <;>
    simp [kernel, kernelCost, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] ; omega

theorem kernelProgram_trace (bs : List Block) (v p : Bool) (rest zero one : Word)
    (a : Accumulator) (ho : a.outer = []) (hg : a.groups = []) (ht : a.terms = []) :
    Trace kernelProgram (kernelCost zero one bs + 1)
      ((state v p (encodeBlocks bs ++ rest) zero one a).withPC (some kernelProgram.entry))
      ((state false false rest zero one (emit (momentCode zero one bs) a)).withPC none) :=
  StructuredCalls.compiled_halt_trace (kernel_eval bs v p rest zero one a ho hg ht) 0 3

/-- The traversal count sums individual payload costs. No product of inner
list lengths occurs in the actual loop bound. -/
theorem scanCost_le_input {α : Type*} (encode : α → Word) (cost : α → ℕ)
    (xs : List α) (a b : ℕ) (hcost : ∀ x ∈ xs, cost x ≤ a * (encode x).length + b) :
    scanCost encode cost xs ≤ (a + b + 18) * (Encoding.encodeList encode xs).length := by
  induction xs with
  | nil => simp [scanCost]
  | cons x xs ih =>
      have hx := hcost x (by simp)
      have ht := ih (fun y hy => hcost y (by simp [hy]))
      simp only [scanCost, List.map_cons, List.sum_cons] at *
      rw [Encoding.length_encodeList_cons]
      nlinarith

theorem termCost_le_input (t : Term) : termCost t ≤ 7 * (encodeTerm t).length := by
  simp [termCost, encodeTerm, Encoding.length_encodeList_cons]
  omega

theorem groupCost_le_input (zero : Word) (ts : List Term) :
    groupCost zero ts ≤ 30 * (encodeGroup ts).length + (8 * zero.length + 14) := by
  have hs := scanCost_le_input encodeTerm termCost ts 7 0
    (fun t _ => by simpa using termCost_le_input t)
  have hl := Encoding.length_encodeList_lower encodeTerm ts
  unfold groupCost encodeGroup
  nlinarith

theorem blockCost_le_input (zero one : Word) (b : Block) :
    blockCost zero one b ≤
      (8 * zero.length + 8 * one.length + 100) * (encodeBlock b).length := by
  have hs := scanCost_le_input encodeGroup (groupCost zero) b.groups 30
    (8 * zero.length + 14) (fun ts _ => groupCost_le_input zero ts)
  have hl := Encoding.length_encodeList_lower encodeGroup b.groups
  unfold blockCost encodeBlock
  simp only [Encoding.length_encodeList_cons, Encoding.length_encodeList_nil, id_eq]
  nlinarith

theorem kernelCost_le_input (zero one : Word) (bs : List Block) :
    kernelCost zero one bs ≤
      (16 * zero.length + 8 * one.length + 136) * (encodeBlocks bs).length := by
  have hs := scanCost_le_input encodeBlock (blockCost zero one) bs
    (8 * zero.length + 8 * one.length + 100) 0
    (fun b _ => by simpa using blockCost_le_input zero one b)
  have hl := Encoding.length_encodeList_lower encodeBlock bs
  have hone : 1 ≤ (encodeBlocks bs).length := by exact le_trans (by omega) hl
  have hmul := Nat.mul_le_mul_left (8 * zero.length + 13) hone
  unfold kernelCost encodeBlocks at *
  nlinarith

theorem kernelCost_quadratic (zero one : Word) (bs : List Block) :
    kernelCost zero one bs ≤ 136 * (encodeInput zero one bs).length ^ 2 := by
  have hk := kernelCost_le_input zero one bs
  have hn : (encodeInput zero one bs).length =
      2 * zero.length + 2 * one.length + 2 * (encodeBlocks bs).length + 7 := by
    simp [encodeInput, Encoding.length_encodeList_cons]
    omega
  have hc : 16 * zero.length + 8 * one.length + 136 ≤
      136 * (encodeInput zero one bs).length := by omega
  have hl : (encodeBlocks bs).length ≤ (encodeInput zero one bs).length := by omega
  have hm := Nat.mul_le_mul hc hl
  nlinarith

/-! ## Forward-output service boundary -/

abbrev transferOutput : Cmd 3 8 := .call (StackRoutines.transferProgram 3 0 0 1)

theorem transferOutput_eval (v p : Bool) (src zero one : Word) (a : Accumulator) :
    Eval transferOutput (3 * a.output.length + 3)
      (state v p src zero one a)
      (state false false (a.output.reverse ++ src) zero one { a with output := [] }) := by
  let d := state v p src zero one a
  let final := state false false (a.output.reverse ++ src) zero one { a with output := [] }
  have hregs : readRegs d.regs 0 1 none = final.regs := by
    funext i
    fin_cases i <;> simp [d, final, state, readRegs, SubexpHornerProgram.triple]
  have hstacks : StackRoutines.transferStacks (3 : Fin 8) 0 d.stacks = final.stacks := by
    funext i
    fin_cases i <;> simp [d, final, state, StackRoutines.transferStacks]
  have h := StackRoutines.transferProgram_trace (r := 3) (s := 8) 3 0 0 1
    (by decide) (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  simp only [StackRoutines.transferResult] at hh
  rw [hregs, hstacks] at hh
  apply Eval.call
  simpa [transferOutput, StructuredProgram.State.withPC,
    d, final, state, Nat.add_assoc] using hh

def emptyAccumulator : Accumulator := ⟨[], [], [], []⟩

/-- Data boundary with cleared Boolean registers and explicit constant ports. -/
def serviceState (source zero one : Word) : State 3 8 :=
  ⟨fun _ => false, (state false false source zero one emptyAccumulator).stacks⟩

abbrev sourceConstructor : Cmd 3 8 :=
  atom (.set 2 true) ;; kernel ;; transferOutput ;; atom (.set 2 false)

abbrev program : Program 3 8 (StructuredCalls.size sourceConstructor + 1) :=
  StructuredCalls.compiled sourceConstructor 0 0

/-- The program's control table is fixed independently of every input size. -/
theorem sourceConstructor_size : StructuredCalls.size sourceConstructor = 163 := rfl

abbrev fixedProgram : Program 3 8 164 := program

theorem constructor_eval (zero one : Word) (bs : List Block) :
    Eval sourceConstructor (kernelCost zero one bs + 3 * (momentCode zero one bs).length + 5)
      (serviceState (encodeBlocks bs) zero one)
      (serviceState (momentCode zero one bs) zero one) := by
  have heq : (StructuredProgram.Atom.set (s := 8) (2 : Fin 3) true).eval
      (serviceState (encodeBlocks bs) zero one) =
      state false false (encodeBlocks bs) zero one emptyAccumulator := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr,
        serviceState, state, SubexpHornerProgram.triple]
    · rfl
  have henter : Eval (atom (.set 2 true)) 1 (serviceState (encodeBlocks bs) zero one)
      (state false false (encodeBlocks bs) zero one emptyAccumulator) := by
    rw [← heq]
    exact .base (.atom _ _)
  have hk := kernel_eval bs false false [] zero one emptyAccumulator rfl rfl rfl
  have ht := transferOutput_eval false false [] zero one
    (emit (momentCode zero one bs) emptyAccumulator)
  have heq' : (StructuredProgram.Atom.set (s := 8) (2 : Fin 3) false).eval
      (state false false (momentCode zero one bs) zero one emptyAccumulator) =
      serviceState (momentCode zero one bs) zero one := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr, state, SubexpHornerProgram.triple]
    · rfl
  have hexit : Eval (atom (.set 2 false)) 1
      (state false false (momentCode zero one bs) zero one emptyAccumulator)
      (serviceState (momentCode zero one bs) zero one) := by
    rw [← heq']
    exact .base (.atom _ _)
  simp only [List.append_nil] at hk
  have ht' : Eval transferOutput (3 * (momentCode zero one bs).length + 3)
      (state false false [] zero one (emit (momentCode zero one bs) emptyAccumulator))
      (state false false (momentCode zero one bs) zero one emptyAccumulator) := by
    simpa [emit, emptyAccumulator] using ht
  convert Eval.seq henter (Eval.seq hk (Eval.seq ht' hexit)) using 1 ;
    simp [Nat.add_comm, Nat.add_left_comm] ; omega

/-- The fixed source program emits the interpreter's exact postfix input,
preserving the supplied zero/one payloads and clearing its work ports. -/
theorem program_trace (zero one : Word) (bs : List Block) :
    Trace program (kernelCost zero one bs + 3 * (momentCode zero one bs).length + 6)
      ((serviceState (encodeBlocks bs) zero one).withPC (some program.entry))
      ((serviceState (momentCode zero one bs) zero one).withPC none) := by
  have h := StructuredCalls.compiled_halt_trace (constructor_eval zero one bs) 0 0
  exact h

theorem program_expression_trace {R : Type*} [Zero R] [One R] (encode : R → Word)
    (bs : List (SubexpAlgorithm.Block R)) :
    Trace program
      (kernelCost (encode 0) (encode 1) (bs.map (ofBlock encode)) +
        3 * (SubexpPostfixControl.serializeCode encode
          (SubexpAlgorithm.momentExpression bs).compile).length + 6)
      ((serviceState (encodeBlocks (bs.map (ofBlock encode))) (encode 0) (encode 1)).withPC
        (some program.entry))
      ((serviceState (SubexpPostfixControl.serializeCode encode
          (SubexpAlgorithm.momentExpression bs).compile) (encode 0) (encode 1)).withPC none) := by
  simpa only [momentCode_eq] using program_trace (encode 0) (encode 1) (bs.map (ofBlock encode))

@[simp] theorem pushWord_length (x : Word) : (pushWord x).length = 2 * x.length + 2 := by
  simp [pushWord]

@[simp] theorem operators_length (mul : Bool) (n : ℕ) :
    (operators mul n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [operators_succ, List.length_append, ih]; simp [operator]; omega

theorem flattenedCode_le_scanCost {α : Type*} (encode code : α → Word) (cost : α → ℕ)
    (xs : List α) (h : ∀ x ∈ xs, (code x).length ≤ cost x) :
    ((xs.map code).flatten).length ≤ scanCost encode cost xs := by
  induction xs with
  | nil => simp [scanCost]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons, List.flatten_cons, List.length_append,
        scanCost, List.sum_cons] at *
      omega

theorem termCode_length_le (t : Term) : (termCode t).length ≤ termCost t := by
  simp [termCode, termCost, operator]
  omega

theorem groupCode_length_le (zero : Word) (ts : List Term) :
    (groupCode zero ts).length ≤ groupCost zero ts := by
  have h := flattenedCode_le_scanCost encodeTerm termCode termCost ts (fun t _ => termCode_length_le t)
  simp only [groupCode, List.length_append, pushWord_length, operators_length, groupCost]
  omega

theorem blockCode_length_le (zero one : Word) (b : Block) :
    (blockCode zero one b).length ≤ blockCost zero one b := by
  have h := flattenedCode_le_scanCost encodeGroup (groupCode zero) (groupCost zero)
    b.groups (fun ts _ => groupCode_length_le zero ts)
  simp only [blockCode, productCode, List.length_append, pushWord_length,
    operators_length, blockCost, operator, List.length_cons, List.length_nil]
  omega

theorem momentCode_length_le (zero one : Word) (bs : List Block) :
    (momentCode zero one bs).length ≤ kernelCost zero one bs := by
  have h := flattenedCode_le_scanCost encodeBlock (blockCode zero one) (blockCost zero one)
    bs (fun b _ => blockCode_length_le zero one b)
  simp only [momentCode, List.length_append, pushWord_length, operators_length, kernelCost]
  omega

/-- The fixed finite source program has a quadratic upper bound in the
combined encoded data size, including both reusable constant payloads. -/
theorem program_runsIn (zero one : Word) (bs : List Block) :
    RunsIn program (550 * ((encodeInput zero one bs).length + 1) ^ 2)
      ((serviceState (encodeBlocks bs) zero one).withPC (some program.entry))
      ((serviceState (momentCode zero one bs) zero one).withPC none) := by
  refine ⟨_, ?_, program_trace zero one bs⟩
  have hk := kernelCost_quadratic zero one bs
  have hl := momentCode_length_le zero one bs
  have hs : (encodeInput zero one bs).length ^ 2 ≤
      ((encodeInput zero one bs).length + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hp : 1 ≤ ((encodeInput zero one bs).length + 1) ^ 2 := by
    calc
      1 = 1 ^ 2 := rfl
      _ ≤ ((encodeInput zero one bs).length + 1) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
  have hscaled := Nat.mul_le_mul_left 544 hs
  omega

theorem primitive_execution (zero one : Word) (bs : List Block) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program *
        (550 * ((encodeInput zero one bs).length + 1) ^ 2))
      (BitProgram.primitiveCfg program
        ((serviceState (encodeBlocks bs) zero one).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((serviceState (momentCode zero one bs) zero one).withPC none)) :=
  BitProgram.primitive_execution program (program_runsIn zero one bs)

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram

namespace OAI.Algorithms

/-! Fixed nested source emitter and its actual byte-level execution bound. -/
namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word Accumulator pushWord operator operators emit bump
  state counterWord setCounter counterPort popTag unframe emitFramedLiteral emitLiteral
  emitOperator countOne drain scan scanCost)

local infixr:60 " ;; " => Cmd.seq

abbrev productBody : Cmd 3 8 := scan factorBody ;; emitLiteral 2 ;; drain 6 true

def productCost (one x : Word) (fs : List (Factor Word)) : ℕ :=
  scanCost encodeFactor (factorCost x) fs + 8 * one.length + 4 * fs.length + 13

theorem productBody_eval (fs : List (Factor Word)) (source zero one x : Word)
    (a : Accumulator) (hx : a.outer = x) (hprod : a.groups = []) :
    Eval productBody (productCost one x fs)
      (state false false (Encoding.encodeList encodeFactor fs ++ source) zero one a)
      (state false false source zero one (emit (productCode one x fs) a)) := by
  let pre := (fs.map (factorCode x)).flatten
  let pending := List.replicate fs.length true
  have hs := SubexpKernelControl.scan_eval factorBody encodeFactor (factorCost x)
    (factorUpdate x) (fun a => a.outer = x) zero one false true
    (fun f rest a ha => by simpa only [ha] using factorBody_eval f rest zero one a)
    (fun f a ha => by simpa [factorUpdate, bump, setCounter, emit] using ha)
    fs false false source a hx
  have hs' : Eval (scan factorBody) (2 + scanCost encodeFactor (factorCost x) fs)
      (state false false (Encoding.encodeList encodeFactor fs ++ source) zero one a)
      (state false true source zero one (emit pre (setCounter 1 pending a))) := by
    simpa [factorUpdate, SubexpKernelControl.fold_bump_emit, pre, pending, counterWord, hprod] using hs
  have ho := SubexpKernelControl.emitLiteral_eval true false true source zero one
    (emit pre (setCounter 1 pending a))
  have hd := SubexpKernelControl.drain_eval 1 true pending false false source zero one
    (emit (pre ++ pushWord one) a)
  have hd' : Eval (drain 6 true) (4 * fs.length + 2)
      (state false false source zero one (emit (pushWord one) (emit pre (setCounter 1 pending a))))
      (state false false source zero one (emit (productCode one x fs) a)) := by
    have hclear := SubexpKernelControl.setCounter_same (1 : Fin 3) a
    have hword : counterWord (1 : Fin 3) a = [] := hprod
    rw [hword] at hclear
    simpa [counterPort, pending, productCode, pre, SubexpKernelControl.emit_emit,
      SubexpKernelControl.setCounter_emit, hclear, List.append_assoc] using hd
  have ht := hs'.seq (ho.seq hd')
  convert ht using 1 <;> simp [productBody, productCost] ; omega

abbrev termBody : Cmd 3 8 :=
  emitFramedLiteral ;; emitFramedLiteral ;; emitX ;; emitOperator true ;;
    productBody ;; emitOperator true ;; emitOperator true ;; countOne 7

def termCost (one x : Word) (t : Term Word) : ℕ :=
  7 * t.value.length + 7 * t.inverseNode.length + 8 * x.length +
    productCost one x t.factors + 30

def termUpdate (one x : Word) (t : Term Word) (a : Accumulator) : Accumulator :=
  bump 2 (emit (termCode one x t) a)

theorem termBody_eval (t : Term Word) (source zero one x : Word) (a : Accumulator)
    (hx : a.outer = x) (hprod : a.groups = []) :
    Eval termBody (termCost one x t)
      (state false false (encodeTerm t ++ source) zero one a)
      (state false false source zero one (termUpdate one x t a)) := by
  let tail := Encoding.encodeList encodeFactor t.factors ++ source
  let a1 := emit (pushWord t.value) a
  let a2 := emit (pushWord t.inverseNode) a1
  let a3 := emit (pushWord x) a2
  let a4 := emit (operator true) a3
  let a5 := emit (productCode one x t.factors) a4
  let a6 := emit (operator true) a5
  let a7 := emit (operator true) a6
  have h1 := SubexpKernelControl.emitFramedLiteral_eval false false t.value
    (Encoding.frame t.inverseNode ++ tail) zero one a
  have h2 := SubexpKernelControl.emitFramedLiteral_eval false true t.inverseNode tail zero one a1
  have h3 := emitX_eval false true tail zero one a2
  have h4 := SubexpKernelControl.emitOperator_eval true false false tail zero one a3
  have h5 := productBody_eval t.factors source zero one x a4
    (by simpa [a4, a3, a2, a1, emit] using hx) (by simpa [a4, a3, a2, a1, emit] using hprod)
  have h6 := SubexpKernelControl.emitOperator_eval true false false source zero one a5
  have h7 := SubexpKernelControl.emitOperator_eval true false false source zero one a6
  have h8 := SubexpKernelControl.countOne_eval 2 false false source zero one a7
  have h3' : Eval emitX (8 * x.length + 9) (state false true tail zero one a2)
      (state false false tail zero one a3) := by
    simpa [a2, a1, a3, emit, hx] using h3
  have ht := h1.seq (h2.seq (h3'.seq (h4.seq (h5.seq (h6.seq (h7.seq h8))))))
  convert ht using 1
  all_goals simp [termBody, termCost, termUpdate, termCode, encodeTerm, tail,
    a1, a2, a3, a4, a5, a6, a7, SubexpKernelControl.emit_emit, bump,
    counterPort, List.append_assoc]
  all_goals omega

abbrev rowBody : Cmd 3 8 :=
  emitFramedLiteral ;; scan termBody ;; emitLiteral 1 ;; drain 7 false ;; emitOperator false

def rowCost (zero one x : Word) (r : Row Word) : ℕ :=
  7 * r.delta.length + scanCost encodeTerm (termCost one x) r.terms +
    8 * zero.length + 5 * r.terms.length + 23

theorem rowBody_eval (r : Row Word) (v p : Bool) (source zero one x : Word)
    (a : Accumulator) (hx : a.outer = x) (hprod : a.groups = []) (hsum : a.terms = []) :
    Eval rowBody (rowCost zero one x r)
      (state v p (encodeRow r ++ source) zero one a)
      (state false false source zero one (emit (rowCode zero one x r) a)) := by
  let a0 := emit (pushWord r.delta) a
  let pre := (r.terms.map (termCode one x)).flatten
  let pending := List.replicate r.terms.length true
  have h0 := SubexpKernelControl.emitFramedLiteral_eval v p r.delta
    (Encoding.encodeList encodeTerm r.terms ++ source) zero one a
  have hs := SubexpKernelControl.scan_eval termBody encodeTerm (termCost one x)
    (termUpdate one x) (fun a => a.outer = x ∧ a.groups = []) zero one false false
    (fun t rest a ha => termBody_eval t rest zero one x a ha.1 ha.2)
    (fun t a ha => by simpa [termUpdate, bump, setCounter, emit] using ha)
    r.terms false true source a0 (by simpa [a0, emit] using And.intro hx hprod)
  have hs' : Eval (scan termBody) (2 + scanCost encodeTerm (termCost one x) r.terms)
      (state false true (Encoding.encodeList encodeTerm r.terms ++ source) zero one a0)
      (state false true source zero one (emit pre (setCounter 2 pending a0))) := by
    simp only [termUpdate] at hs
    rw [SubexpKernelControl.fold_bump_emit] at hs
    simpa [pre, pending, counterWord, a0, emit, hsum] using hs
  have hz := SubexpKernelControl.emitLiteral_eval false false true source zero one
    (emit pre (setCounter 2 pending a0))
  have hd := SubexpKernelControl.drain_eval 2 false pending false false source zero one
    (emit (pre ++ pushWord zero) a0)
  have hd' : Eval (drain 7 false) (5 * r.terms.length + 2)
      (state false false source zero one (emit (pushWord zero) (emit pre (setCounter 2 pending a0))))
      (state false false source zero one
        (emit (pre ++ pushWord zero ++ operators false r.terms.length) a0)) := by
    have hclear := SubexpKernelControl.setCounter_same (2 : Fin 3) a0
    have hword : counterWord (2 : Fin 3) a0 = [] := by simpa [a0, counterWord, emit] using hsum
    rw [hword] at hclear
    simpa [counterPort, pending, SubexpKernelControl.emit_emit,
      SubexpKernelControl.setCounter_emit, hclear, List.append_assoc] using hd
  have ha := SubexpKernelControl.emitOperator_eval false false false source zero one
    (emit (pre ++ pushWord zero ++ operators false r.terms.length) a0)
  have ht := h0.seq (hs'.seq (hz.seq (hd'.seq ha)))
  convert ht using 1
  all_goals simp [rowBody, rowCost, rowCode, encodeRow, pre, a0,
    SubexpKernelControl.emit_emit, List.append_assoc]
  all_goals omega


private theorem copyX_eval (which v p : Bool) (source zero one : Word) (a : Accumulator) :
    Eval (.call (StackRoutines.copyProgram (if which then 2 else 1) (5 : Fin 8) 4 (0 : Fin 3) 1))
      (7 * (if which then one else zero).length + 5)
      (state v p source zero one a)
      (state false false source zero one
        {a with outer := (if which then one else zero) ++ a.outer}) := by
  let d := state v p source zero one a
  have ht := ListRegisterProgram.copy_run (if which then (2 : Fin 8) else 1) 5 4 (0 : Fin 3) 1
    (by cases which <;> decide) (by cases which <;> decide) (by decide) (by decide)
    d.regs d.stacks (by rfl)
  have hf : (⟨readRegs d.regs 0 1 none,
      StackRoutines.copyStacks (if which then 2 else 1) 5 d.stacks⟩ : State 3 8) =
      state false false source zero one {a with outer := (if which then one else zero) ++ a.outer} := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [d, state, readRegs, SubexpHornerProgram.triple]
    · funext i; cases which <;> fin_cases i <;> simp [d, state, StackRoutines.copyStacks]
  have he := Eval.call _ (a := d)
    (b := (⟨readRegs d.regs 0 1 none,
      StackRoutines.copyStacks (if which then 2 else 1) 5 d.stacks⟩ : State 3 8)) ht
  change Eval _ _ d _ at he
  rw [hf] at he
  cases which <;> simpa [d, state] using he

abbrev prepareX : Cmd 3 8 :=
  .call (StackRoutines.copyProgram (2 : Fin 8) 5 4 (0 : Fin 3) 1) ;;
    .call (StackRoutines.copyProgram (1 : Fin 8) 5 4 (0 : Fin 3) 1)

theorem prepareX_eval (v p : Bool) (source zero one : Word) (a : Accumulator) (hx : a.outer = []) :
    Eval prepareX (7 * (zero.length + one.length) + 10)
      (state v p source zero one a)
      (state false false source zero one {a with outer := zero ++ one}) := by
  have h1 := copyX_eval true v p source zero one a
  have h2 := copyX_eval false false false source zero one {a with outer := one ++ a.outer}
  have h := h1.seq h2
  convert h using 1 <;> simp [prepareX, hx] ; omega

abbrev clearX : Cmd 3 8 := .call (StackRoutines.clearProgram (5 : Fin 8) (0 : Fin 3) 1)

theorem clearX_eval (v p : Bool) (source zero one : Word) (a : Accumulator) :
    Eval clearX (2 * a.outer.length + 3) (state v p source zero one a)
      (state false false source zero one {a with outer := []}) := by
  let d := state v p source zero one a
  have ht := ListRegisterProgram.clear_run (5 : Fin 8) (0 : Fin 3) 1 d.regs d.stacks
  have hf : (⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 5 d.stacks⟩ : State 3 8) =
      state false false source zero one {a with outer := []} := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [d, state, readRegs, SubexpHornerProgram.triple]
    · funext i; fin_cases i <;> simp [d, state, StackRoutines.clearStacks]
  have he := Eval.call _ (a := d)
    (b := (⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 5 d.stacks⟩ : State 3 8)) ht
  change Eval _ _ d _ at he
  rw [hf] at he
  simpa [clearX, d, state] using he

abbrev command : Cmd 3 8 :=
  .base (.atom (.set 2 true)) ;; prepareX ;; rowBody ;; clearX ;;
    SubexpKernelControl.transferOutput ;; .base (.atom (.set 2 false))

abbrev program : Program 3 8 (size command + 1) := compiled command 0 0

def commandCost (zero one : Word) (r : Row Word) : ℕ :=
  rowCost zero one (zero ++ one) r + 9 * (zero.length + one.length) +
    3 * (rowCode zero one (zero ++ one) r).length + 18

theorem command_eval (zero one : Word) (r : Row Word) :
    Eval command (commandCost zero one r)
      (SubexpKernelControl.serviceState (encodeRow r) zero one)
      (SubexpKernelControl.serviceState (rowCode zero one (zero ++ one) r) zero one) := by
  let empty := SubexpKernelControl.emptyAccumulator
  let prepared : Accumulator := {empty with outer := zero ++ one}
  let output := rowCode zero one (zero ++ one) r
  have hin : (StructuredProgram.Atom.set (s := 8) (2 : Fin 3) true).eval
      (SubexpKernelControl.serviceState (encodeRow r) zero one) =
      state false false (encodeRow r) zero one empty := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr,
        SubexpKernelControl.serviceState, state, SubexpHornerProgram.triple]
    · rfl
  have henter : Eval (.base (.atom (.set 2 true))) 1
      (SubexpKernelControl.serviceState (encodeRow r) zero one)
      (state false false (encodeRow r) zero one empty) := by
    rw [← hin]
    exact .base (.atom _ _)
  have hp := prepareX_eval false false (encodeRow r) zero one empty rfl
  have hr := rowBody_eval r false false [] zero one (zero ++ one) prepared rfl rfl rfl
  have hc := clearX_eval false false [] zero one (emit output prepared)
  have ht := SubexpKernelControl.transferOutput_eval false false [] zero one (emit output empty)
  have heq : (StructuredProgram.Atom.set (s := 8) (2 : Fin 3) false).eval
      (state false false output zero one empty) =
      SubexpKernelControl.serviceState output zero one := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr, state, SubexpHornerProgram.triple]
    · rfl
  have hexit : Eval (.base (.atom (.set 2 false))) 1 (state false false output zero one empty)
      (SubexpKernelControl.serviceState output zero one) := by
    rw [← heq]
    exact .base (.atom _ _)
  have hr' : Eval rowBody (rowCost zero one (zero ++ one) r)
      (state false false (encodeRow r) zero one prepared)
      (state false false [] zero one (emit output prepared)) := by simpa [output] using hr
  have hc' : Eval clearX (2 * (zero.length + one.length) + 3)
      (state false false [] zero one (emit output prepared))
      (state false false [] zero one (emit output empty)) := by
    simpa [prepared, empty, emit, SubexpKernelControl.emptyAccumulator] using hc
  have ht' : Eval SubexpKernelControl.transferOutput (3 * output.length + 3)
      (state false false [] zero one (emit output empty))
      (state false false output zero one empty) := by
    simpa [empty, emit, SubexpKernelControl.emptyAccumulator] using ht
  have h := henter.seq (hp.seq (hr'.seq (hc'.seq (ht'.seq hexit))))
  convert h using 1 ; simp [ commandCost, output] ; omega

theorem program_trace (zero one : Word) (r : Row Word) :
    Trace program (commandCost zero one r + 1)
      ((SubexpKernelControl.serviceState (encodeRow r) zero one).withPC (some program.entry))
      ((SubexpKernelControl.serviceState (rowCode zero one (zero ++ one) r) zero one).withPC none) :=
  compiled_halt_trace (command_eval zero one r) 0 0


theorem factorCost_le_input (x : Word) (f : Factor Word) :
    factorCost x f ≤ 7 * (encodeFactor f).length + (8 * x.length + 29) := by
  simp [factorCost, encodeFactor]
  omega

theorem productCost_le_input (one x : Word) (fs : List (Factor Word)) :
    productCost one x fs ≤ (8 * x.length + 60) * (Encoding.encodeList encodeFactor fs).length +
      (8 * one.length + 13) := by
  have hs := SubexpKernelControl.scanCost_le_input encodeFactor (factorCost x) fs
    7 (8 * x.length + 29) (fun f _ => factorCost_le_input x f)
  have hl := Encoding.length_encodeList_lower encodeFactor fs
  unfold productCost
  nlinarith

theorem termCost_le_input (one x : Word) (t : Term Word) :
    termCost one x t ≤ (16 * x.length + 16 * one.length + 200) * (encodeTerm t).length := by
  have hp := productCost_le_input one x t.factors
  have hl := Encoding.length_encodeList_lower encodeFactor t.factors
  unfold termCost encodeTerm
  simp only [List.length_append, Encoding.length_frame]
  nlinarith [Nat.zero_le (x.length * t.value.length), Nat.zero_le (x.length * t.inverseNode.length),
    Nat.zero_le (one.length * t.value.length), Nat.zero_le (one.length * t.inverseNode.length),
    Nat.zero_le (one.length * (Encoding.encodeList encodeFactor t.factors).length)]

theorem rowCost_le_input (zero one x : Word) (r : Row Word) :
    rowCost zero one x r ≤
      (16 * x.length + 16 * one.length + 16 * zero.length + 300) * (encodeRow r).length := by
  have hs := SubexpKernelControl.scanCost_le_input encodeTerm (termCost one x) r.terms
    (16 * x.length + 16 * one.length + 200) 0
    (fun t _ => by simpa using termCost_le_input one x t)
  have hl := Encoding.length_encodeList_lower encodeTerm r.terms
  unfold rowCost encodeRow
  simp only [List.length_append, Encoding.length_frame]
  nlinarith [Nat.zero_le (x.length * r.delta.length), Nat.zero_le (one.length * r.delta.length),
    Nat.zero_le (zero.length * r.delta.length),
    Nat.zero_le (zero.length * (Encoding.encodeList encodeTerm r.terms).length)]

theorem factorCode_length_le (x : Word) (f : Factor Word) :
    (factorCode x f).length ≤ factorCost x f := by
  simp [factorCode, factorCost, operator, SubexpKernelControl.pushWord_length]
  omega

theorem productCode_length_le (one x : Word) (fs : List (Factor Word)) :
    (productCode one x fs).length ≤ productCost one x fs := by
  have h := SubexpKernelControl.flattenedCode_le_scanCost encodeFactor (factorCode x)
    (factorCost x) fs (fun f _ => factorCode_length_le x f)
  simp only [productCode, List.length_append, SubexpKernelControl.pushWord_length,
    SubexpKernelControl.operators_length, productCost]
  omega

theorem termCode_length_le (one x : Word) (t : Term Word) :
    (termCode one x t).length ≤ termCost one x t := by
  have hp := productCode_length_le one x t.factors
  simp only [termCode, List.length_append, SubexpKernelControl.pushWord_length,
    operator, List.length_cons, List.length_nil, termCost]
  omega

theorem rowCode_length_le (zero one x : Word) (r : Row Word) :
    (rowCode zero one x r).length ≤ rowCost zero one x r := by
  have h := SubexpKernelControl.flattenedCode_le_scanCost encodeTerm (termCode one x)
    (termCost one x) r.terms (fun t _ => termCode_length_le one x t)
  simp only [rowCode, List.length_append, SubexpKernelControl.pushWord_length,
    SubexpKernelControl.operators_length, operator, List.length_cons, List.length_nil, rowCost]
  omega

def inputSize (zero one : Word) (r : Row Word) : ℕ :=
  zero.length + one.length + (encodeRow r).length + 1

theorem rowCost_quadratic (zero one : Word) (r : Row Word) :
    rowCost zero one (zero ++ one) r ≤ 300 * inputSize zero one r ^ 2 := by
  have h := rowCost_le_input zero one (zero ++ one) r
  simp only [List.length_append] at h
  have hc : 16 * (zero.length + one.length) + 16 * one.length + 16 * zero.length + 300 ≤
      300 * inputSize zero one r := by unfold inputSize; omega
  have hl : (encodeRow r).length ≤ inputSize zero one r := by unfold inputSize; omega
  have hm := Nat.mul_le_mul hc hl
  nlinarith

theorem program_runsIn (zero one : Word) (r : Row Word) :
    RunsIn program (2048 * inputSize zero one r ^ 2)
      ((SubexpKernelControl.serviceState (encodeRow r) zero one).withPC (some program.entry))
      ((SubexpKernelControl.serviceState (rowCode zero one (zero ++ one) r) zero one).withPC none) := by
  refine ⟨_, ?_, program_trace zero one r⟩
  have hr := rowCost_quadratic zero one r
  have hc := rowCode_length_le zero one (zero ++ one) r
  have hn : 1 ≤ inputSize zero one r := by unfold inputSize; omega
  have hl : zero.length + one.length ≤ inputSize zero one r := by unfold inputSize; omega
  have hs : inputSize zero one r ≤ inputSize zero one r ^ 2 := by nlinarith
  unfold commandCost
  nlinarith

theorem primitive_execution (zero one : Word) (r : Row Word) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * (2048 * inputSize zero one r ^ 2))
      (BitProgram.primitiveCfg program
        ((SubexpKernelControl.serviceState (encodeRow r) zero one).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((SubexpKernelControl.serviceState (rowCode zero one (zero ++ one) r) zero one).withPC none)) :=
  BitProgram.primitive_execution program (program_runsIn zero one r)


def mapFactor {A B : Type*} (f : A → B) (a : Factor A) : Factor B :=
  ⟨f a.inverseDifference, f a.negativeNode⟩

def mapTerm {A B : Type*} (f : A → B) (a : Term A) : Term B :=
  ⟨f a.value, f a.inverseNode, a.factors.map (mapFactor f)⟩

def mapRow {A B : Type*} (f : A → B) (a : Row A) : Row B :=
  ⟨f a.delta, a.terms.map (mapTerm f)⟩

theorem factorCode_eq {R : Type*} (encode : R → Word) (x : R) (f : Factor R) :
    factorCode (encode x) (mapFactor encode f) =
      SubexpPostfixControl.serializeCode encode (factorExpression x f).compile := by
  simp [factorCode, mapFactor, factorExpression, Algorithm.Expr.compile, SubexpPostfixControl.serializeCode,
    SubexpPostfixControl.serializeInstr, pushWord, operator, List.append_assoc]

theorem productCode_eq {R : Type*} [One R] (encode : R → Word) (x : R) (fs : List (Factor R)) :
    productCode (encode 1) (encode x) (fs.map (mapFactor encode)) =
      SubexpPostfixControl.serializeCode encode
        (Algorithm.Expr.product (fs.map (factorExpression x))).compile := by
  rw [SubexpKernelControl.compile_product]
  simp [productCode, List.map_map, Function.comp_def, factorCode_eq]

theorem termCode_eq {R : Type*} [One R] (encode : R → Word) (x : R) (t : Term R) :
    termCode (encode 1) (encode x) (mapTerm encode t) =
      SubexpPostfixControl.serializeCode encode (termExpression x t).compile := by
  simp [termCode, mapTerm, termExpression, Algorithm.Expr.compile,
    SubexpKernelControl.serializeCode_append, productCode_eq,
    SubexpPostfixControl.serializeCode, SubexpPostfixControl.serializeInstr,
    pushWord, operator, List.append_assoc]

theorem rowCode_eq {R : Type*} [Zero R] [One R] (encode : R → Word) (x : R) (r : Row R) :
    rowCode (encode 0) (encode 1) (encode x) (mapRow encode r) =
      SubexpPostfixControl.serializeCode encode (rowExpression x r).compile := by
  simp only [rowCode, mapRow, List.map_map, Function.comp_def, termCode_eq,
    rowExpression, Algorithm.Expr.compile, SubexpKernelControl.serializeCode_append,
    SubexpKernelControl.compile_sum]
  simp [SubexpPostfixControl.serializeCode, SubexpPostfixControl.serializeInstr,
    pushWord, operator, List.append_assoc]

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms

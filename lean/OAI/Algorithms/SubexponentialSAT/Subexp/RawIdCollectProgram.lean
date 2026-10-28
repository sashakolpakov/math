import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.RawIdEncoding
import OAI.Algorithms.SubexponentialSAT.Subexp.FactorPacketRows

namespace OAI.Algorithms

/-! Fixed parser-based collection of the identifiers that actually occur.
The program consumes nested clause records and emits reversed identifier
records. It never converts an identifier to a natural-number counter. -/

namespace SubexponentialSAT.Subexp.RawIdCollectProgram

open BitProgram StructuredCalls RawIdEncoding

abbrev Data := State 8 22

structure View where
  source : Word
  capturedClause : Word
  clause : Word
  capturedLiteral : Word
  literalWord : Word
  identifier : Word
  output : Word

def store (v : View) : Fin 22 → Word := fun i =>
  if i = 0 then v.source else if i = 1 then v.capturedClause else if i = 2 then v.clause
  else if i = 3 then v.capturedLiteral else if i = 4 then v.literalWord
  else if i = 5 then v.identifier else if i = 6 then v.output else []

def state (regs : Fin 8 → Bool) (v : View) : Data := ⟨regs, store v⟩

def clauseState (regs : Fin 8 → Bool) (source clause output : Word) : Data :=
  state regs ⟨source, [], clause, [], [], [], output⟩

def resting (regs : Fin 8 → Bool) (source output : Word) : Data :=
  clauseState regs source [] output

@[simp] theorem store_source (v : View) : store v 0 = v.source := rfl
@[simp] theorem update_source (v : View) (w : Word) :
    Function.update (store v) 0 w = store {v with source := w} := by
  funext j; by_cases h : j = 0 <;> simp [store, h]

@[simp] theorem store_capturedClause (v : View) : store v 1 = v.capturedClause := rfl
@[simp] theorem update_capturedClause (v : View) (w : Word) :
    Function.update (store v) 1 w = store {v with capturedClause := w} := by
  funext j; by_cases h : j = 1 <;> simp [store, h]

@[simp] theorem store_clause (v : View) : store v 2 = v.clause := rfl
@[simp] theorem update_clause (v : View) (w : Word) :
    Function.update (store v) 2 w = store {v with clause := w} := by
  funext j; by_cases h : j = 2 <;> simp [store, h]

@[simp] theorem store_capturedLiteral (v : View) : store v 3 = v.capturedLiteral := rfl
@[simp] theorem update_capturedLiteral (v : View) (w : Word) :
    Function.update (store v) 3 w = store {v with capturedLiteral := w} := by
  funext j; by_cases h : j = 3 <;> simp [store, h]

@[simp] theorem store_literalWord (v : View) : store v 4 = v.literalWord := rfl
@[simp] theorem update_literalWord (v : View) (w : Word) :
    Function.update (store v) 4 w = store {v with literalWord := w} := by
  funext j; by_cases h : j = 4 <;> simp [store, h]

@[simp] theorem store_identifier (v : View) : store v 5 = v.identifier := rfl
@[simp] theorem update_identifier (v : View) (w : Word) :
    Function.update (store v) 5 w = store {v with identifier := w} := by
  funext j; by_cases h : j = 5 <;> simp [store, h]

@[simp] theorem store_output (v : View) : store v 6 = v.output := rfl
@[simp] theorem update_output (v : View) (w : Word) :
    Function.update (store v) 6 w = store {v with output := w} := by
  funext j; by_cases h : j = 6 <;> simp [store, h]

abbrev readClause : Cmd 8 22 := SubexpInputFrames.readField 0 1 (by decide)

theorem readClause_eval (regs : Fin 8 → Bool) (v : View) (bits tail : Word) :
    ∃ rf, Eval readClause (6 * bits.length + 4)
      (state regs {v with source := Encoding.frame bits ++ tail, capturedClause := []})
      (state rf {v with source := tail, capturedClause := bits.reverse}) := by
  obtain ⟨e, he, hs⟩ := SubexpInputFrames.readField_execute 0 1 (by decide)
    (state regs {v with source := Encoding.frame bits ++ tail, capturedClause := []}) bits tail rfl rfl
  have heq : e = state e.regs {v with source := tail, capturedClause := bits.reverse} := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · simpa only [state, update_source, update_capturedClause] using hs
  exact ⟨e.regs, by rw [heq] at he; exact he⟩

abbrev readLiteral : Cmd 8 22 := SubexpInputFrames.readField 2 3 (by decide)

theorem readLiteral_eval (regs : Fin 8 → Bool) (v : View) (bits tail : Word) :
    ∃ rf, Eval readLiteral (6 * bits.length + 4)
      (state regs {v with clause := Encoding.frame bits ++ tail, capturedLiteral := []})
      (state rf {v with clause := tail, capturedLiteral := bits.reverse}) := by
  obtain ⟨e, he, hs⟩ := SubexpInputFrames.readField_execute 2 3 (by decide)
    (state regs {v with clause := Encoding.frame bits ++ tail, capturedLiteral := []}) bits tail rfl rfl
  have heq : e = state e.regs {v with clause := tail, capturedLiteral := bits.reverse} := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · simpa only [state, update_clause, update_capturedLiteral] using hs
  exact ⟨e.regs, by rw [heq] at he; exact he⟩

abbrev readIdentifier : Cmd 8 22 := SubexpInputFrames.readField 4 5 (by decide)

theorem readIdentifier_eval (regs : Fin 8 → Bool) (v : View) (bits tail : Word) :
    ∃ rf, Eval readIdentifier (6 * bits.length + 4)
      (state regs {v with literalWord := Encoding.frame bits ++ tail, identifier := []})
      (state rf {v with literalWord := tail, identifier := bits.reverse}) := by
  obtain ⟨e, he, hs⟩ := SubexpInputFrames.readField_execute 4 5 (by decide)
    (state regs {v with literalWord := Encoding.frame bits ++ tail, identifier := []}) bits tail rfl rfl
  have heq : e = state e.regs {v with literalWord := tail, identifier := bits.reverse} := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · simpa only [state, update_literalWord, update_identifier] using hs
  exact ⟨e.regs, by rw [heq] at he; exact he⟩

abbrev restoreClause : Cmd 8 22 := .call (StackRoutines.transferProgram 1 2 0 1)

theorem restoreClause_eval (regs : Fin 8 → Bool) (v : View) (bits : Word) :
    Eval restoreClause (3 * bits.length + 3)
      (state regs {v with capturedClause := bits.reverse, clause := []})
      (state (readRegs regs 0 1 none) {v with capturedClause := [], clause := bits}) := by
  have h := TupleProgram.transfer_eval (1 : Fin 22) 2 (0 : Fin 8) 1 (by decide) (by decide)
    (state regs {v with capturedClause := bits.reverse, clause := []})
  simpa only [state, StackRoutines.transferStacks, store_capturedClause, store_clause,
    List.length_reverse, List.reverse_reverse, List.append_nil, update_capturedClause, update_clause] using h

abbrev restoreLiteral : Cmd 8 22 := .call (StackRoutines.transferProgram 3 4 0 1)

theorem restoreLiteral_eval (regs : Fin 8 → Bool) (v : View) (bits : Word) :
    Eval restoreLiteral (3 * bits.length + 3)
      (state regs {v with capturedLiteral := bits.reverse, literalWord := []})
      (state (readRegs regs 0 1 none) {v with capturedLiteral := [], literalWord := bits}) := by
  have h := TupleProgram.transfer_eval (3 : Fin 22) 4 (0 : Fin 8) 1 (by decide) (by decide)
    (state regs {v with capturedLiteral := bits.reverse, literalWord := []})
  simpa only [state, StackRoutines.transferStacks, store_capturedLiteral, store_literalWord,
    List.length_reverse, List.reverse_reverse, List.append_nil, update_capturedLiteral, update_literalWord] using h

abbrev dropPolarity : Cmd 8 22 := .base (.atom (.pop 4 0 1))

theorem dropPolarity_eval (regs : Fin 8 → Bool) (v : View) (positive : Bool) :
    Eval dropPolarity 1 (state regs {v with literalWord := [positive]})
      (state (readRegs regs 0 1 (some positive)) {v with literalWord := []}) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.pop (4 : Fin 22) (0 : Fin 8) 1)
    (state regs {v with literalWord := [positive]}))
  simpa only [dropPolarity, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
    state, store_literalWord, update_literalWord, List.head?_cons, List.tail_cons] using h

def emitPorts : Fin 4 ↪ Fin 22 := ⟨![0, 7, 6, 5], by decide⟩
@[simp] theorem emitPorts_two : emitPorts 2 = 6 := rfl
@[simp] theorem emitPorts_three : emitPorts 3 = 5 := rfl

abbrev emitIdentifier : Cmd 8 22 := FactorPacketRows.emitAt emitPorts

theorem emitIdentifier_eval (regs : Fin 8 → Bool) (v : View) (bits : Word) :
    ∃ rf, Eval emitIdentifier (5 * bits.length + 7)
      (state regs {v with identifier := bits.reverse})
      (state rf {v with identifier := [], output := TupleProgram.prependRecord bits v.output}) := by
  obtain ⟨rf, h⟩ := FactorPacketRows.emitAt_eval emitPorts
    (state regs {v with identifier := bits.reverse}) bits rfl
  exact ⟨rf, by simpa only [state, emitPorts_two, emitPorts_three, store_output,
    update_identifier, update_output] using h⟩

abbrev literalCommand : Cmd 8 22 := .seq readLiteral (.seq restoreLiteral
  (.seq readIdentifier (.seq dropPolarity emitIdentifier)))

def literalCost (l : Literal) : ℕ :=
  9 * (literalBytes l).length + 11 * l.variable.length + 19

theorem literal_eval (regs : Fin 8 → Bool) (source tail output : Word) (l : Literal) :
    ∃ rf, Eval literalCommand (literalCost l)
      (clauseState regs source (Encoding.frame (literalBytes l) ++ tail) output)
      (clauseState rf source tail (TupleProgram.prependRecord l.variable output)) := by
  let v0 : View := ⟨source, [], Encoding.frame (literalBytes l) ++ tail, [], [], [], output⟩
  let v1 := {v0 with clause := tail, capturedLiteral := (literalBytes l).reverse}
  let v2 := {v1 with capturedLiteral := [], literalWord := literalBytes l}
  let v3 := {v2 with literalWord := [l.positive], identifier := l.variable.reverse}
  let v4 := {v3 with literalWord := []}
  obtain ⟨r1, h1⟩ := readLiteral_eval regs v0 (literalBytes l) tail
  change Eval readLiteral _ (state regs v0) (state r1 v1) at h1
  have h2 := restoreLiteral_eval r1 v1 (literalBytes l)
  change Eval restoreLiteral _ (state r1 v1) (state (readRegs r1 0 1 none) v2) at h2
  obtain ⟨r3, h3⟩ := readIdentifier_eval (readRegs r1 0 1 none) v2 l.variable [l.positive]
  change Eval readIdentifier _ (state (readRegs r1 0 1 none) v2) (state r3 v3) at h3
  have h4 := dropPolarity_eval r3 v3 l.positive
  change Eval dropPolarity _ (state r3 v3) (state (readRegs r3 0 1 (some l.positive)) v4) at h4
  obtain ⟨rf, h5⟩ := emitIdentifier_eval (readRegs r3 0 1 (some l.positive)) v4 l.variable
  refine ⟨rf, ?_⟩
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  have hc : (6 * (literalBytes l).length + 4) + ((3 * (literalBytes l).length + 3) +
      ((6 * l.variable.length + 4) + (1 + (5 * l.variable.length + 7)))) = literalCost l := by
    unfold literalCost; omega
  rw [hc] at h
  simpa [literalCommand, v0, v1, v2, v3, v4, clauseState, state] using h

abbrev clauseTag : Cmd 8 22 := SubexpInputFrames.readTag 2

theorem clauseTag_eval (regs : Fin 8 → Bool) (source tail output : Word) (flag : Bool) :
    ∃ rf, Eval clauseTag 1 (clauseState regs source (flag :: tail) output)
      (clauseState rf source tail output) ∧ rf 7 = flag := by
  obtain ⟨e, he, hs, hf⟩ := SubexpInputFrames.readTag_execute 2
    (clauseState regs source (flag :: tail) output) flag tail rfl
  have heq : e = clauseState e.regs source tail output := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · simpa only [clauseState, state, update_clause] using hs
  exact ⟨e.regs, by rw [heq] at he; exact he, hf⟩

def listFlag {A : Type*} : List A → Bool
  | [] => false
  | _ :: _ => true

def afterClause : Clause → Word → Word
  | [], tail => tail
  | l :: rest, tail => Encoding.frame (literalBytes l) ++ (clauseBytes rest ++ tail)

theorem clause_tag (C : Clause) (tail : Word) :
    clauseBytes C ++ tail = listFlag C :: afterClause C tail := by
  cases C <;> simp [clauseBytes, Encoding.encodeList, listFlag, afterClause, List.append_assoc]

abbrev clauseLoop : Cmd 8 22 := .while 7 (.seq literalCommand clauseTag)

def clauseBudget : Clause → ℕ
  | [] => 0
  | l :: rest => literalCost l + 2 + clauseBudget rest

theorem clauseLoop_eval (C : Clause) (regs : Fin 8 → Bool) (source tail : Word)
    (acc : List Word) (hg : regs 7 = listFlag C) :
    ∃ t ≤ clauseBudget C + 1, ∃ rf,
      Eval clauseLoop t
        (clauseState regs source (afterClause C tail) (Encoding.encodeList id acc))
        (clauseState rf source tail
          (Encoding.encodeList id ((C.map SAT.Literal.variable).reverse ++ acc))) := by
  induction C generalizing regs acc with
  | nil =>
      refine ⟨1, by simp [clauseBudget], regs, ?_⟩
      simpa only [afterClause, List.map_nil, List.reverse_nil, List.nil_append] using
        (Eval.while_false (body := .seq literalCommand clauseTag)
          (a := clauseState regs source tail (Encoding.encodeList id acc)) hg)
  | cons l rest ih =>
      obtain ⟨rb, hb⟩ := literal_eval regs source (clauseBytes rest ++ tail)
        (Encoding.encodeList id acc) l
      change Eval literalCommand (literalCost l) _
        (clauseState rb source (clauseBytes rest ++ tail)
          (Encoding.encodeList id (l.variable :: acc))) at hb
      obtain ⟨rt, ht, hrt⟩ := clauseTag_eval rb source (afterClause rest tail)
        (Encoding.encodeList id (l.variable :: acc)) (listFlag rest)
      rw [← clause_tag] at ht
      obtain ⟨nl, hnl, rf, hl⟩ := ih rt (l.variable :: acc) hrt
      refine ⟨literalCost l + 1 + nl + 1, ?_, rf, ?_⟩
      · simp only [clauseBudget]; omega
      · have h := Eval.while_true (by exact hg) (hb.seq ht) hl
        simpa only [clauseLoop, afterClause, List.map_cons, List.reverse_cons,
          List.append_assoc, List.singleton_append] using h

abbrev collectClause : Cmd 8 22 := .seq clauseTag clauseLoop

theorem collectClause_eval (C : Clause) (regs : Fin 8 → Bool) (source : Word) (acc : List Word) :
    ∃ t ≤ clauseBudget C + 2, ∃ rf,
      Eval collectClause t
        (clauseState regs source (clauseBytes C) (Encoding.encodeList id acc))
        (resting rf source (Encoding.encodeList id ((C.map SAT.Literal.variable).reverse ++ acc))) := by
  obtain ⟨rt, ht, hrt⟩ := clauseTag_eval regs source (afterClause C [])
    (Encoding.encodeList id acc) (listFlag C)
  rw [← clause_tag, List.append_nil] at ht
  obtain ⟨nl, hnl, rf, hl⟩ := clauseLoop_eval C rt source [] acc hrt
  exact ⟨1 + nl, by omega, rf, ht.seq hl⟩

abbrev clauseCommand : Cmd 8 22 := .seq readClause (.seq restoreClause collectClause)
def clauseCost (C : Clause) : ℕ := 9 * (clauseBytes C).length + 9 + clauseBudget C

theorem clause_eval (C : Clause) (regs : Fin 8 → Bool) (tail : Word) (acc : List Word) :
    ∃ t ≤ clauseCost C, ∃ rf,
      Eval clauseCommand t
        (resting regs (Encoding.frame (clauseBytes C) ++ tail) (Encoding.encodeList id acc))
        (resting rf tail (Encoding.encodeList id ((C.map SAT.Literal.variable).reverse ++ acc))) := by
  let v0 : View := ⟨Encoding.frame (clauseBytes C) ++ tail, [], [], [], [], [], Encoding.encodeList id acc⟩
  let v1 := {v0 with source := tail, capturedClause := (clauseBytes C).reverse}
  let v2 := {v1 with capturedClause := [], clause := clauseBytes C}
  obtain ⟨r1, h1⟩ := readClause_eval regs v0 (clauseBytes C) tail
  change Eval readClause _ (state regs v0) (state r1 v1) at h1
  have h2 := restoreClause_eval r1 v1 (clauseBytes C)
  change Eval restoreClause _ (state r1 v1) (state (readRegs r1 0 1 none) v2) at h2
  obtain ⟨nc, hnc, rf, hc⟩ := collectClause_eval C (readRegs r1 0 1 none) tail acc
  refine ⟨_, ?_, rf, h1.seq (h2.seq hc)⟩
  unfold clauseCost; omega

abbrev formulaTag : Cmd 8 22 := SubexpInputFrames.readTag 0

theorem formulaTag_eval (regs : Fin 8 → Bool) (tail output : Word) (flag : Bool) :
    ∃ rf, Eval formulaTag 1 (resting regs (flag :: tail) output)
      (resting rf tail output) ∧ rf 7 = flag := by
  obtain ⟨e, he, hs, hf⟩ := SubexpInputFrames.readTag_execute 0
    (resting regs (flag :: tail) output) flag tail rfl
  have heq : e = resting e.regs tail output := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · simpa only [resting, clauseState, state, update_source] using hs
  exact ⟨e.regs, by rw [heq] at he; exact he, hf⟩

def afterFormula : Formula → Word → Word
  | [], tail => tail
  | C :: rest, tail => Encoding.frame (clauseBytes C) ++ (encode rest ++ tail)

theorem formula_tag (F : Formula) (tail : Word) :
    encode F ++ tail = listFlag F :: afterFormula F tail := by
  cases F <;> simp [encode, Encoding.encodeList, listFlag, afterFormula, List.append_assoc]

abbrev formulaLoop : Cmd 8 22 := .while 7 (.seq clauseCommand formulaTag)

def formulaBudget : Formula → ℕ
  | [] => 0
  | C :: rest => clauseCost C + 2 + formulaBudget rest

theorem formulaLoop_eval (F : Formula) (regs : Fin 8 → Bool) (tail : Word) (acc : List Word)
    (hg : regs 7 = listFlag F) :
    ∃ t ≤ formulaBudget F + 1, ∃ rf,
      Eval formulaLoop t
        (resting regs (afterFormula F tail) (Encoding.encodeList id acc))
        (resting rf tail (Encoding.encodeList id ((ids F).reverse ++ acc))) := by
  induction F generalizing regs acc with
  | nil =>
      refine ⟨1, by simp [formulaBudget], regs, ?_⟩
      simpa only [afterFormula, ids, List.flatten_nil, List.map_nil,
        List.reverse_nil, List.nil_append] using
        (Eval.while_false (body := .seq clauseCommand formulaTag)
          (a := resting regs tail (Encoding.encodeList id acc)) hg)
  | cons C rest ih =>
      obtain ⟨nc, hnc, rc, hc⟩ := clause_eval C regs (encode rest ++ tail) acc
      obtain ⟨rt, ht, hrt⟩ := formulaTag_eval rc (afterFormula rest tail)
        (Encoding.encodeList id ((C.map SAT.Literal.variable).reverse ++ acc)) (listFlag rest)
      rw [← formula_tag] at ht
      obtain ⟨nl, hnl, rf, hl⟩ := ih rt ((C.map SAT.Literal.variable).reverse ++ acc) hrt
      refine ⟨nc + 1 + nl + 1, ?_, rf, ?_⟩
      · simp only [formulaBudget]; omega
      · have h := Eval.while_true (by exact hg) (hc.seq ht) hl
        simpa only [formulaLoop, afterFormula, ids, List.flatten_cons,
          List.map_append, List.reverse_append, List.append_assoc] using h

abbrev seed : Cmd 8 22 := TupleProgram.pushConst 6 0 false

theorem seed_eval (regs : Fin 8 → Bool) (source : Word) :
    Eval seed 2 (resting regs source [])
      (resting (Function.update regs 0 false) source [false]) := by
  simpa only [resting, clauseState, state, TupleProgram.pushedState,
    store_output, update_output] using
    TupleProgram.pushConst_eval (6 : Fin 22) (0 : Fin 8) false (resting regs source [])

abbrev command : Cmd 8 22 := .seq seed (.seq formulaTag formulaLoop)
def program := compiled command (0 : Fin 22) 6

theorem program_runsIn (regs : Fin 8 → Bool) (F : Formula) :
    ∃ rf, RunsIn program (formulaBudget F + 5)
      ((resting regs (encode F) []).withPC (some program.entry))
      ((resting rf [] (Encoding.encodeList id (ids F).reverse)).withPC none) := by
  have hs := seed_eval regs (encode F)
  obtain ⟨rt, ht, hrt⟩ := formulaTag_eval (Function.update regs 0 false)
    (afterFormula F []) [false] (listFlag F)
  rw [← formula_tag, List.append_nil] at ht
  obtain ⟨nl, hnl, rf, hl⟩ := formulaLoop_eval F rt [] [] hrt
  simp only [List.append_nil] at hl
  exact ⟨rf, 2 + (1 + nl) + 1, by omega, compiled_halt_trace (hs.seq (ht.seq hl)) 0 6⟩

theorem literalCost_le (l : Literal) : literalCost l + 2 ≤ 25 * ((literalBytes l).length + 1) := by
  rw [literalCost, literalBytes_length]
  omega

theorem clauseBudget_le (C : Clause) : clauseBudget C ≤ 25 * (clauseBytes C).length := by
  induction C with
  | nil => simp [clauseBudget, clauseBytes, Encoding.encodeList]
  | cons l rest ih =>
      have h := literalCost_le l
      simp only [clauseBudget, clauseBytes, Encoding.length_encodeList_cons] at *
      omega

theorem formulaBudget_le (F : Formula) : formulaBudget F + 5 ≤ 50 * ((encode F).length + 1) := by
  have hmain : formulaBudget F ≤ 45 * (encode F).length := by
    induction F with
    | nil => simp [formulaBudget, encode, Encoding.encodeList]
    | cons C rest ih =>
        have hc := clauseBudget_le C
        simp only [formulaBudget, clauseCost, encode, Encoding.length_encodeList_cons] at *
        omega
  omega

/-- Collection time depends only on raw bytes, including the identifier
bytes, and never on the numeric magnitude of an identifier. -/
theorem program_linear (regs : Fin 8 → Bool) (F : Formula) :
    ∃ rf, RunsIn program (50 * ((encode F).length + 1))
      ((resting regs (encode F) []).withPC (some program.entry))
      ((resting rf [] (Encoding.encodeList id (ids F).reverse)).withPC none) := by
  obtain ⟨rf, n, hn, h⟩ := program_runsIn regs F
  exact ⟨rf, n, hn.trans (formulaBudget_le F), h⟩

theorem lifted_execution {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 22 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (frame : State R S) (regs : Fin 8 → Bool) (F : Formula) :
    ∃ t ≤ 50 * ((encode F).length + 1), ∃ rf,
      Eval (.call (ProgramLinking.liftProgram program register stack)) t
        (embedState register stack frame (resting regs (encode F) []))
        (embedState register stack frame (resting rf [] (Encoding.encodeList id (ids F).reverse))) := by
  obtain ⟨rf, t, ht, he⟩ := program_linear regs F
  exact ⟨t, ht, rf, eval_call_lifted program register stack frame hregister hstack he⟩

theorem primitive_execution (regs : Fin 8 → Bool) (F : Formula) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (50 * ((encode F).length + 1)))
      (primitiveCfg program ((resting regs (encode F) []).withPC (some program.entry)))
      (primitiveCfg program
        ((resting rf [] (Encoding.encodeList id (ids F).reverse)).withPC none)) := by
  obtain ⟨rf, h⟩ := program_linear regs F
  exact ⟨rf, BitProgram.primitive_execution program h⟩

end SubexponentialSAT.Subexp.RawIdCollectProgram

end OAI.Algorithms

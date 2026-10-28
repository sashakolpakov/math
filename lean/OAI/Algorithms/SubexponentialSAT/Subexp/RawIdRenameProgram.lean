import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.RawIdRenaming
import OAI.Algorithms.SubexponentialSAT.SubexpNodeIndexProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.FactorPacketRows

namespace OAI.Algorithms

/-! Actual dictionary-index renaming of raw variable identifiers. The
complete dictionary is scanned by the published byte-comparison program.
Unary signed-literal codes are built from the returned unary rank. -/

namespace SubexponentialSAT.Subexp.RawIdRenameProgram

open BitProgram StructuredCalls RawIdEncoding

abbrev Data := State 8 22

structure View where
  source : Word
  capturedClause : Word
  clause : Word
  capturedId : Word
  dictionary : Word
  capturedLiteral : Word
  rank : Word
  clauseOutput : Word
  output : Word
  literalWord : Word
  encoded : Word
  query : Word

def store (v : View) : Fin 22 → Word := fun i =>
  if i = 0 then v.source else if i = 1 then v.capturedClause else if i = 2 then v.clause
  else if i = 3 then v.capturedId else if i = 4 then v.dictionary
  else if i = 5 then v.capturedLiteral else if i = 6 then v.rank
  else if i = 7 then v.clauseOutput else if i = 8 then v.output
  else if i = 9 then v.literalWord else if i = 14 then v.encoded
  else if i = 15 then v.query else []

def state (regs : Fin 8 → Bool) (v : View) : Data := ⟨regs, store v⟩

def baseView (dictionary source clause clauseOutput output : Word) : View :=
  ⟨source, [], clause, [], dictionary, [], [], clauseOutput, output, [], [], []⟩

def clauseState (regs : Fin 8 → Bool) (dictionary source clause clauseOutput output : Word) : Data :=
  state regs (baseView dictionary source clause clauseOutput output)

def resting (regs : Fin 8 → Bool) (dictionary source output : Word) : Data :=
  clauseState regs dictionary source [] [] output

def codeIn (dictionary : List Word) (l : Literal) : ℕ :=
  2 * dictionary.idxOf l.variable + if l.positive then 1 else 0

def clauseCodes (dictionary : List Word) (C : Clause) : List ℕ := (C.map (codeIn dictionary)).reverse
def formulaCodes (dictionary : List Word) (F : Formula) : List (List ℕ) :=
  (F.map (clauseCodes dictionary)).reverse

def clauseResult (dictionary : List Word) (C : Clause) : Word :=
  Encoding.encodeList Encoding.encodeNat (clauseCodes dictionary C)

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

@[simp] theorem store_capturedId (v : View) : store v 3 = v.capturedId := rfl
@[simp] theorem update_capturedId (v : View) (w : Word) :
    Function.update (store v) 3 w = store {v with capturedId := w} := by
  funext j; by_cases h : j = 3 <;> simp [store, h]

@[simp] theorem store_dictionary (v : View) : store v 4 = v.dictionary := rfl
@[simp] theorem update_dictionary (v : View) (w : Word) :
    Function.update (store v) 4 w = store {v with dictionary := w} := by
  funext j; by_cases h : j = 4 <;> simp [store, h]

@[simp] theorem store_capturedLiteral (v : View) : store v 5 = v.capturedLiteral := rfl
@[simp] theorem update_capturedLiteral (v : View) (w : Word) :
    Function.update (store v) 5 w = store {v with capturedLiteral := w} := by
  funext j; by_cases h : j = 5 <;> simp [store, h]

@[simp] theorem store_rank (v : View) : store v 6 = v.rank := rfl
@[simp] theorem update_rank (v : View) (w : Word) :
    Function.update (store v) 6 w = store {v with rank := w} := by
  funext j; by_cases h : j = 6 <;> simp [store, h]

@[simp] theorem store_clauseOutput (v : View) : store v 7 = v.clauseOutput := rfl
@[simp] theorem update_clauseOutput (v : View) (w : Word) :
    Function.update (store v) 7 w = store {v with clauseOutput := w} := by
  funext j; by_cases h : j = 7 <;> simp [store, h]

@[simp] theorem store_output (v : View) : store v 8 = v.output := rfl
@[simp] theorem update_output (v : View) (w : Word) :
    Function.update (store v) 8 w = store {v with output := w} := by
  funext j; by_cases h : j = 8 <;> simp [store, h]

@[simp] theorem store_literalWord (v : View) : store v 9 = v.literalWord := rfl
@[simp] theorem update_literalWord (v : View) (w : Word) :
    Function.update (store v) 9 w = store {v with literalWord := w} := by
  funext j; by_cases h : j = 9 <;> simp [store, h]

@[simp] theorem store_encoded (v : View) : store v 14 = v.encoded := rfl
@[simp] theorem update_encoded (v : View) (w : Word) :
    Function.update (store v) 14 w = store {v with encoded := w} := by
  funext j; by_cases h : j = 14 <;> simp [store, h]

@[simp] theorem store_query (v : View) : store v 15 = v.query := rfl
@[simp] theorem update_query (v : View) (w : Word) :
    Function.update (store v) 15 w = store {v with query := w} := by
  funext j; by_cases h : j = 15 <;> simp [store, h]

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

abbrev readLiteral : Cmd 8 22 := SubexpInputFrames.readField 2 5 (by decide)

theorem readLiteral_eval (regs : Fin 8 → Bool) (v : View) (bits tail : Word) :
    ∃ rf, Eval readLiteral (6 * bits.length + 4)
      (state regs {v with clause := Encoding.frame bits ++ tail, capturedLiteral := []})
      (state rf {v with clause := tail, capturedLiteral := bits.reverse}) := by
  obtain ⟨e, he, hs⟩ := SubexpInputFrames.readField_execute 2 5 (by decide)
    (state regs {v with clause := Encoding.frame bits ++ tail, capturedLiteral := []}) bits tail rfl rfl
  have heq : e = state e.regs {v with clause := tail, capturedLiteral := bits.reverse} := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · simpa only [state, update_clause, update_capturedLiteral] using hs
  exact ⟨e.regs, by rw [heq] at he; exact he⟩

abbrev readIdentifier : Cmd 8 22 := SubexpInputFrames.readField 9 3 (by decide)

theorem readIdentifier_eval (regs : Fin 8 → Bool) (v : View) (bits tail : Word) :
    ∃ rf, Eval readIdentifier (6 * bits.length + 4)
      (state regs {v with literalWord := Encoding.frame bits ++ tail, capturedId := []})
      (state rf {v with literalWord := tail, capturedId := bits.reverse}) := by
  obtain ⟨e, he, hs⟩ := SubexpInputFrames.readField_execute 9 3 (by decide)
    (state regs {v with literalWord := Encoding.frame bits ++ tail, capturedId := []}) bits tail rfl rfl
  have heq : e = state e.regs {v with literalWord := tail, capturedId := bits.reverse} := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · simpa only [state, update_literalWord, update_capturedId] using hs
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

abbrev restoreLiteral : Cmd 8 22 := .call (StackRoutines.transferProgram 5 9 0 1)

theorem restoreLiteral_eval (regs : Fin 8 → Bool) (v : View) (bits : Word) :
    Eval restoreLiteral (3 * bits.length + 3)
      (state regs {v with capturedLiteral := bits.reverse, literalWord := []})
      (state (readRegs regs 0 1 none) {v with capturedLiteral := [], literalWord := bits}) := by
  have h := TupleProgram.transfer_eval (5 : Fin 22) 9 (0 : Fin 8) 1 (by decide) (by decide)
    (state regs {v with capturedLiteral := bits.reverse, literalWord := []})
  simpa only [state, StackRoutines.transferStacks, store_capturedLiteral, store_literalWord,
    List.length_reverse, List.reverse_reverse, List.append_nil, update_capturedLiteral, update_literalWord] using h

abbrev restoreIdentifier : Cmd 8 22 := .call (StackRoutines.transferProgram 3 15 0 1)

theorem restoreIdentifier_eval (regs : Fin 8 → Bool) (v : View) (bits : Word) :
    Eval restoreIdentifier (3 * bits.length + 3)
      (state regs {v with capturedId := bits.reverse, query := []})
      (state (readRegs regs 0 1 none) {v with capturedId := [], query := bits}) := by
  have h := TupleProgram.transfer_eval (3 : Fin 22) 15 (0 : Fin 8) 1 (by decide) (by decide)
    (state regs {v with capturedId := bits.reverse, query := []})
  simpa only [state, StackRoutines.transferStacks, store_capturedId, store_query,
    List.length_reverse, List.reverse_reverse, List.append_nil, update_capturedId, update_query] using h

abbrev readPolarity : Cmd 8 22 := .base (.atom (.pop 9 5 1))

theorem readPolarity_eval (regs : Fin 8 → Bool) (v : View) (positive : Bool) :
    Eval readPolarity 1 (state regs {v with literalWord := [positive]})
      (state (readRegs regs 5 1 (some positive)) {v with literalWord := []}) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.pop (9 : Fin 22) (5 : Fin 8) 1)
    (state regs {v with literalWord := [positive]}))
  simpa only [readPolarity, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
    state, store_literalWord, update_literalWord, List.head?_cons, List.tail_cons] using h

def indexRegisters : Fin 5 → Fin 8 := Fin.castAdd 3
def indexPorts : Fin 7 → Fin 22 := ![15, 4, 10, 11, 12, 13, 6]
theorem indexRegisters_injective : Function.Injective indexRegisters := Fin.castAdd_injective _ _
theorem indexPorts_injective : Function.Injective indexPorts := by decide

def indexProgram := compiled SubexpNodeIndexProgram.Internal.command (0 : Fin 7) 6
abbrev findIndex : Cmd 8 22 := .call (ProgramLinking.liftProgram indexProgram indexRegisters indexPorts)

private theorem index_stacks (frame : Data) (inner : State 5 7) (target : Fin 22 → Word)
    (hp : ∀ i, target (indexPorts i) = inner.stacks i)
    (hf : ∀ i, (¬ ∃ j, indexPorts j = i) → target i = frame.stacks i) :
    (embedState indexRegisters indexPorts frame inner).stacks = target := by
  funext i
  by_cases h : ∃ j, indexPorts j = i
  · obtain ⟨j, rfl⟩ := h
    exact (embedState_stack _ _ _ _ indexPorts_injective j).trans (hp j).symm
  · exact (embedState_stack_frame _ _ _ _ _ h).trans (hf i h).symm

private theorem index_input (regs : Fin 8 → Bool) (v : View) :
    embedState indexRegisters indexPorts (state regs {v with rank := []})
      (SubexpNodeIndexProgram.Internal.state (regs ∘ indexRegisters)
        v.query v.dictionary [] [] [] [] []) = state regs {v with rank := []} := by
  apply embedState_eq_of_ports _ _ _ _ _ indexRegisters_injective indexPorts_injective
  · intro i; rfl
  · intros; rfl
  · intro i; fin_cases i <;> rfl
  · intros; rfl

theorem findIndex_eval (regs : Fin 8 → Bool) (v : View) (dictionary : List Word) (query : Word) :
    ∃ t ≤ SubexpNodeIndexProgram.Internal.budget query dictionary, ∃ rf,
      Eval findIndex t
        (state regs {v with dictionary := ProgramEncoding.encodeRecords dictionary, query := query, rank := []})
        (state rf {v with dictionary := ProgramEncoding.encodeRecords dictionary, query := query, rank := List.replicate (dictionary.idxOf query) true}) ∧ rf 5 = regs 5 := by
  let a := state regs {v with dictionary := ProgramEncoding.encodeRecords dictionary, query := query, rank := []}
  obtain ⟨t, ht, rr, he⟩ := SubexpNodeIndexProgram.Internal.command_eval
    (regs ∘ indexRegisters) query dictionary
  have hr := compiled_halt_trace he (0 : Fin 7) 6
  have h := eval_call_lifted indexProgram indexRegisters indexPorts a
    indexRegisters_injective indexPorts_injective hr
  have ha : embedState indexRegisters indexPorts a
      (SubexpNodeIndexProgram.Internal.state (regs ∘ indexRegisters) query
        (ProgramEncoding.encodeRecords dictionary) [] [] [] [] []) = a :=
    index_input regs {v with dictionary := ProgramEncoding.encodeRecords dictionary, query := query}
  rw [ha] at h
  let b := SubexpNodeIndexProgram.Internal.state rr query (ProgramEncoding.encodeRecords dictionary)
    [] [] [] [] (List.replicate (dictionary.idxOf query) true)
  let rf := (embedState indexRegisters indexPorts a b).regs
  have hs := index_stacks a b
    (store {v with dictionary := ProgramEncoding.encodeRecords dictionary, query := query, rank := List.replicate (dictionary.idxOf query) true})
    (by intro i; fin_cases i <;> rfl)
    (by
      intro i hi
      have h6 : i ≠ 6 := fun h => hi ⟨6, h.symm⟩
      simp only [a, state, store, h6, ite_false])
  have hb : embedState indexRegisters indexPorts a b =
      state rf {v with dictionary := ProgramEncoding.encodeRecords dictionary, query := query, rank := List.replicate (dictionary.idxOf query) true} := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · exact hs
  change Eval findIndex (t + 1) a (embedState indexRegisters indexPorts a b) at h
  rw [hb] at h
  refine ⟨t + 1, ht, rf, h, ?_⟩
  exact embedState_register_frame _ _ _ _ 5 (by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    have := i.isLt
    change i.val = 5 at hv
    omega)

abbrev copyRank : Cmd 8 22 := .call (StackRoutines.copyProgram 6 14 13 0 1)
abbrev moveRank : Cmd 8 22 := .call (StackRoutines.transferProgram 6 14 0 1)

theorem copyRank_eval (regs : Fin 8 → Bool) (v : View) (n : ℕ) :
    Eval copyRank (7 * n + 5)
      (state regs {v with rank := List.replicate n true, encoded := []})
      (state (readRegs regs 0 1 none) {v with rank := List.replicate n true, encoded := List.replicate n true}) := by
  have h := TupleProgram.copy_eval (6 : Fin 22) 14 13 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide)
    (state regs {v with rank := List.replicate n true, encoded := []}) rfl
  simpa only [state, StackRoutines.copyStacks, store_rank, store_encoded,
    List.length_replicate, List.append_nil, update_encoded] using h

theorem moveRank_eval (regs : Fin 8 → Bool) (v : View) (n : ℕ) :
    Eval moveRank (3 * n + 3)
      (state regs {v with rank := List.replicate n true, encoded := List.replicate n true})
      (state (readRegs regs 0 1 none) {v with rank := [], encoded := List.replicate (2 * n) true}) := by
  have h := TupleProgram.transfer_eval (6 : Fin 22) 14 (0 : Fin 8) 1 (by decide) (by decide)
    (state regs {v with rank := List.replicate n true, encoded := List.replicate n true})
  simpa only [state, StackRoutines.transferStacks, store_rank, store_encoded,
    List.length_replicate, List.reverse_replicate, ← List.replicate_add, ← two_mul,
    update_rank, update_encoded] using h

abbrev addPolarity : Cmd 8 22 := .ite 5 (TupleProgram.pushConst 14 0 true) (.base .skip)

theorem addPolarity_eval (regs : Fin 8 → Bool) (v : View) (n : ℕ) (positive : Bool)
    (hp : regs 5 = positive) :
    ∃ t ≤ 3, ∃ rf, Eval addPolarity t
      (state regs {v with encoded := List.replicate (2 * n) true})
      (state rf {v with encoded := List.replicate (2 * n + if positive then 1 else 0) true}) := by
  cases positive with
  | false =>
      refine ⟨1, by decide, regs, ?_⟩
      simpa using (Eval.ite_false (yes := TupleProgram.pushConst 14 0 true) hp (Eval.base (StructuredProgram.Eval.skip
        (state regs {v with encoded := List.replicate (2 * n) true}))))
  | true =>
      have h := TupleProgram.pushConst_eval (14 : Fin 22) (0 : Fin 8) true
        (state regs {v with encoded := List.replicate (2 * n) true})
      have hb := Eval.ite_true (test := (5 : Fin 8)) (no := .base .skip) hp h
      refine ⟨3, by decide, Function.update regs 0 true, ?_⟩
      simpa [addPolarity, TupleProgram.pushedState, state, ← List.replicate_succ] using hb

abbrev terminateCode : Cmd 8 22 := TupleProgram.pushConst 14 0 false

theorem terminateCode_eval (regs : Fin 8 → Bool) (v : View) (n : ℕ) :
    Eval terminateCode 2 (state regs {v with encoded := List.replicate n true})
      (state (Function.update regs 0 false) {v with encoded := (Encoding.encodeNat n).reverse}) := by
  have h := TupleProgram.pushConst_eval (14 : Fin 22) (0 : Fin 8) false
    (state regs {v with encoded := List.replicate n true})
  simpa [terminateCode, TupleProgram.pushedState, state, Encoding.encodeNat] using h

abbrev encodeRank : Cmd 8 22 := .seq copyRank (.seq moveRank (.seq addPolarity terminateCode))

theorem encodeRank_eval (regs : Fin 8 → Bool) (v : View) (n : ℕ) (positive : Bool)
    (hp : regs 5 = positive) :
    ∃ t ≤ 10 * n + 13, ∃ rf, Eval encodeRank t
      (state regs {v with rank := List.replicate n true, encoded := []})
      (state rf {v with rank := [], encoded := (Encoding.encodeNat (2 * n + if positive then 1 else 0)).reverse}) := by
  have h1 := copyRank_eval regs v n
  have h2 := moveRank_eval (readRegs regs 0 1 none) v n
  have hp' : (readRegs (readRegs regs 0 1 none) 0 1 none) 5 = positive := by
    simpa [readRegs] using hp
  obtain ⟨tp, htp, rp, h3⟩ := addPolarity_eval (readRegs (readRegs regs 0 1 none) 0 1 none)
    {v with rank := []} n positive hp'
  have h4 := terminateCode_eval rp {v with rank := []} (2 * n + if positive then 1 else 0)
  exact ⟨_, by omega, _, h1.seq (h2.seq (h3.seq h4))⟩


def literalEmitPorts : Fin 4 ↪ Fin 22 := ⟨![0, 13, 7, 14], by decide⟩
def clauseEmitPorts : Fin 4 ↪ Fin 22 := ⟨![0, 13, 8, 14], by decide⟩
@[simp] theorem literalEmitPorts_two : literalEmitPorts 2 = 7 := rfl
@[simp] theorem literalEmitPorts_three : literalEmitPorts 3 = 14 := rfl
@[simp] theorem clauseEmitPorts_two : clauseEmitPorts 2 = 8 := rfl
@[simp] theorem clauseEmitPorts_three : clauseEmitPorts 3 = 14 := rfl

abbrev emitLiteral : Cmd 8 22 := FactorPacketRows.emitAt literalEmitPorts

theorem emitLiteral_eval (regs : Fin 8 → Bool) (v : View) (code : ℕ) :
    ∃ rf, Eval emitLiteral (5 * (code + 1) + 7)
      (state regs {v with encoded := (Encoding.encodeNat code).reverse})
      (state rf {v with encoded := [], clauseOutput := TupleProgram.prependRecord (Encoding.encodeNat code) v.clauseOutput}) := by
  obtain ⟨rf, h⟩ := FactorPacketRows.emitAt_eval literalEmitPorts
    (state regs {v with encoded := (Encoding.encodeNat code).reverse}) (Encoding.encodeNat code) rfl
  exact ⟨rf, by simpa only [Encoding.length_encodeNat, state, literalEmitPorts_two,
    literalEmitPorts_three, store_clauseOutput, update_encoded, update_clauseOutput] using h⟩

abbrev clearQuery : Cmd 8 22 := .call (StackRoutines.clearProgram 15 0 1)

theorem clearQuery_eval (regs : Fin 8 → Bool) (v : View) :
    Eval clearQuery (2 * v.query.length + 3) (state regs v)
      (state (readRegs regs 0 1 none) {v with query := []}) := by
  have h := TupleProgram.clear_eval (15 : Fin 22) (0 : Fin 8) 1 (state regs v)
  simpa only [state, StackRoutines.clearStacks, store_query, update_query] using h

abbrev literalCommand : Cmd 8 22 := .seq readLiteral (.seq restoreLiteral (.seq readIdentifier
  (.seq restoreIdentifier (.seq readPolarity (.seq findIndex (.seq encodeRank (.seq emitLiteral clearQuery)))))))

def literalBudget (dictionary : List Word) (l : Literal) : ℕ :=
  9 * (literalBytes l).length + 11 * l.variable.length + 10 * dictionary.idxOf l.variable +
    5 * codeIn dictionary l + SubexpNodeIndexProgram.Internal.budget l.variable dictionary + 43

theorem literal_eval (regs : Fin 8 → Bool) (dictionary : List Word)
    (source tail clauseOutput output : Word) (l : Literal) :
    ∃ t ≤ literalBudget dictionary l, ∃ rf,
      Eval literalCommand t
        (clauseState regs (ProgramEncoding.encodeRecords dictionary) source
          (Encoding.frame (literalBytes l) ++ tail) clauseOutput output)
        (clauseState rf (ProgramEncoding.encodeRecords dictionary) source tail
          (TupleProgram.prependRecord (Encoding.encodeNat (codeIn dictionary l)) clauseOutput) output) := by
  let v0 := baseView (ProgramEncoding.encodeRecords dictionary) source
    (Encoding.frame (literalBytes l) ++ tail) clauseOutput output
  let v1 := {v0 with clause := tail, capturedLiteral := (literalBytes l).reverse}
  let v2 := {v1 with capturedLiteral := [], literalWord := literalBytes l}
  let v3 := {v2 with literalWord := [l.positive], capturedId := l.variable.reverse}
  let v4 := {v3 with capturedId := [], query := l.variable}
  let v5 := {v4 with literalWord := []}
  let v6 := {v5 with rank := List.replicate (dictionary.idxOf l.variable) true}
  let v7 := {v6 with rank := [], encoded := (Encoding.encodeNat (codeIn dictionary l)).reverse}
  let v8 := {v7 with encoded := [], clauseOutput := TupleProgram.prependRecord (Encoding.encodeNat (codeIn dictionary l)) clauseOutput}
  obtain ⟨r1, h1⟩ := readLiteral_eval regs v0 (literalBytes l) tail
  change Eval readLiteral _ (state regs v0) (state r1 v1) at h1
  have h2 := restoreLiteral_eval r1 v1 (literalBytes l)
  change Eval restoreLiteral _ (state r1 v1) (state (readRegs r1 0 1 none) v2) at h2
  obtain ⟨r3, h3⟩ := readIdentifier_eval (readRegs r1 0 1 none) v2 l.variable [l.positive]
  change Eval readIdentifier _ (state (readRegs r1 0 1 none) v2) (state r3 v3) at h3
  have h4 := restoreIdentifier_eval r3 v3 l.variable
  change Eval restoreIdentifier _ (state r3 v3) (state (readRegs r3 0 1 none) v4) at h4
  let rp := readRegs (readRegs r3 0 1 none) 5 1 (some l.positive)
  have h5 := readPolarity_eval (readRegs r3 0 1 none) v4 l.positive
  change Eval readPolarity _ (state (readRegs r3 0 1 none) v4) (state rp v5) at h5
  obtain ⟨ni, hni, ri, hi, hflag⟩ := findIndex_eval rp v5 dictionary l.variable
  change Eval findIndex ni (state rp v5) (state ri v6) at hi
  have hflag' : ri 5 = l.positive := by simpa [rp, readRegs] using hflag
  obtain ⟨ne, hne, re, he⟩ := encodeRank_eval ri v6 (dictionary.idxOf l.variable) l.positive hflag'
  change Eval encodeRank ne (state ri v6) (state re v7) at he
  obtain ⟨r8, h8⟩ := emitLiteral_eval re v7 (codeIn dictionary l)
  change Eval emitLiteral _ (state re v7) (state r8 v8) at h8
  have h9 := clearQuery_eval r8 v8
  change Eval clearQuery (2 * l.variable.length + 3) (state r8 v8)
    (clauseState (readRegs r8 0 1 none) (ProgramEncoding.encodeRecords dictionary) source tail
      (TupleProgram.prependRecord (Encoding.encodeNat (codeIn dictionary l)) clauseOutput) output) at h9
  refine ⟨_, ?_, _, h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (hi.seq (he.seq (h8.seq h9)))))))⟩
  unfold literalBudget
  omega

abbrev clauseTag : Cmd 8 22 := SubexpInputFrames.readTag 2

theorem clauseTag_eval (regs : Fin 8 → Bool) (dictionary source tail clauseOutput output : Word)
    (flag : Bool) :
    ∃ rf, Eval clauseTag 1 (clauseState regs dictionary source (flag :: tail) clauseOutput output)
      (clauseState rf dictionary source tail clauseOutput output) ∧ rf 7 = flag := by
  obtain ⟨e, he, hs, hf⟩ := SubexpInputFrames.readTag_execute 2
    (clauseState regs dictionary source (flag :: tail) clauseOutput output) flag tail rfl
  have heq : e = clauseState e.regs dictionary source tail clauseOutput output := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · simpa only [clauseState, baseView, state, update_clause] using hs
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

def clauseBudget (dictionary : List Word) : Clause → ℕ
  | [] => 0
  | l :: rest => literalBudget dictionary l + 2 + clauseBudget dictionary rest

theorem clauseLoop_eval (dictionary : List Word) (C : Clause) (regs : Fin 8 → Bool)
    (source tail output : Word) (acc : List ℕ) (hg : regs 7 = listFlag C) :
    ∃ t ≤ clauseBudget dictionary C + 1, ∃ rf,
      Eval clauseLoop t
        (clauseState regs (ProgramEncoding.encodeRecords dictionary) source (afterClause C tail)
          (Encoding.encodeList Encoding.encodeNat acc) output)
        (clauseState rf (ProgramEncoding.encodeRecords dictionary) source tail
          (Encoding.encodeList Encoding.encodeNat ((C.map (codeIn dictionary)).reverse ++ acc)) output) := by
  induction C generalizing regs acc with
  | nil =>
      refine ⟨1, by simp [clauseBudget], regs, ?_⟩
      simpa only [afterClause, List.map_nil, List.reverse_nil, List.nil_append] using
        (Eval.while_false (body := .seq literalCommand clauseTag)
          (a := clauseState regs (ProgramEncoding.encodeRecords dictionary) source tail
            (Encoding.encodeList Encoding.encodeNat acc) output) hg)
  | cons l rest ih =>
      obtain ⟨nb, hnb, rb, hb⟩ := literal_eval regs dictionary source (clauseBytes rest ++ tail)
        (Encoding.encodeList Encoding.encodeNat acc) output l
      change Eval literalCommand nb _
        (clauseState rb (ProgramEncoding.encodeRecords dictionary) source (clauseBytes rest ++ tail)
          (Encoding.encodeList Encoding.encodeNat (codeIn dictionary l :: acc)) output) at hb
      obtain ⟨rt, ht, hrt⟩ := clauseTag_eval rb (ProgramEncoding.encodeRecords dictionary) source
        (afterClause rest tail) (Encoding.encodeList Encoding.encodeNat (codeIn dictionary l :: acc))
        output (listFlag rest)
      rw [← clause_tag] at ht
      obtain ⟨nl, hnl, rf, hl⟩ := ih rt (codeIn dictionary l :: acc) hrt
      refine ⟨nb + 1 + nl + 1, ?_, rf, ?_⟩
      · simp only [clauseBudget]; omega
      · have h := Eval.while_true (by exact hg) (hb.seq ht) hl
        simpa only [clauseLoop, afterClause, List.map_cons, List.reverse_cons,
          List.append_assoc, List.singleton_append] using h

abbrev collectClause : Cmd 8 22 := .seq clauseTag clauseLoop

theorem collectClause_eval (dictionary : List Word) (C : Clause) (regs : Fin 8 → Bool)
    (source output : Word) :
    ∃ t ≤ clauseBudget dictionary C + 2, ∃ rf,
      Eval collectClause t
        (clauseState regs (ProgramEncoding.encodeRecords dictionary) source (clauseBytes C) [false] output)
        (clauseState rf (ProgramEncoding.encodeRecords dictionary) source [] (clauseResult dictionary C) output) := by
  obtain ⟨rt, ht, hrt⟩ := clauseTag_eval regs (ProgramEncoding.encodeRecords dictionary) source
    (afterClause C []) [false] output (listFlag C)
  rw [← clause_tag, List.append_nil] at ht
  obtain ⟨nl, hnl, rf, hl⟩ := clauseLoop_eval dictionary C rt source [] output [] hrt
  simp only [List.append_nil] at hl
  exact ⟨1 + nl, by omega, rf, ht.seq hl⟩

abbrev emitClause : Cmd 8 22 := .seq (.call (StackRoutines.transferProgram 7 14 0 1))
  (FactorPacketRows.emitAt clauseEmitPorts)

theorem emitClause_eval (regs : Fin 8 → Bool) (v : View) (bits : Word) :
    ∃ rf, Eval emitClause (8 * bits.length + 10)
      (state regs {v with clauseOutput := bits, encoded := []})
      (state rf {v with clauseOutput := [], encoded := [], output := TupleProgram.prependRecord bits v.output}) := by
  have h1 := TupleProgram.transfer_eval (7 : Fin 22) 14 (0 : Fin 8) 1 (by decide) (by decide)
    (state regs {v with clauseOutput := bits, encoded := []})
  have ht : Eval (.call (StackRoutines.transferProgram (7 : Fin 22) 14 (0 : Fin 8) 1))
      (3 * bits.length + 3) (state regs {v with clauseOutput := bits, encoded := []})
      (state (readRegs regs 0 1 none) {v with clauseOutput := [], encoded := bits.reverse}) := by
    simpa only [state, StackRoutines.transferStacks, store_clauseOutput, store_encoded,
      List.append_nil, update_clauseOutput, update_encoded] using h1
  obtain ⟨rf, h2⟩ := FactorPacketRows.emitAt_eval clauseEmitPorts
    (state (readRegs regs 0 1 none) {v with clauseOutput := [], encoded := bits.reverse}) bits rfl
  simp only [state, clauseEmitPorts_two, clauseEmitPorts_three, store_output,
    update_encoded, update_output] at h2
  refine ⟨rf, ?_⟩
  have hc : (3 * bits.length + 3) + (5 * bits.length + 7) = 8 * bits.length + 10 := by omega
  simpa [emitClause, hc, state] using ht.seq h2

abbrev seedClause : Cmd 8 22 := TupleProgram.pushConst 7 0 false

theorem seedClause_eval (regs : Fin 8 → Bool) (v : View) :
    Eval seedClause 2 (state regs {v with clauseOutput := []})
      (state (Function.update regs 0 false) {v with clauseOutput := [false]}) := by
  simpa only [state, TupleProgram.pushedState, store_clauseOutput, update_clauseOutput] using
    TupleProgram.pushConst_eval (7 : Fin 22) (0 : Fin 8) false (state regs {v with clauseOutput := []})

abbrev clauseCommand : Cmd 8 22 := .seq readClause (.seq restoreClause (.seq seedClause
  (.seq collectClause emitClause)))

def clauseCost (dictionary : List Word) (C : Clause) : ℕ :=
  9 * (clauseBytes C).length + 8 * (clauseResult dictionary C).length +
    clauseBudget dictionary C + 21

theorem clause_eval (dictionary : List Word) (C : Clause) (regs : Fin 8 → Bool)
    (tail output : Word) :
    ∃ t ≤ clauseCost dictionary C, ∃ rf,
      Eval clauseCommand t
        (resting regs (ProgramEncoding.encodeRecords dictionary) (Encoding.frame (clauseBytes C) ++ tail) output)
        (resting rf (ProgramEncoding.encodeRecords dictionary) tail
          (TupleProgram.prependRecord (clauseResult dictionary C) output)) := by
  let v0 := baseView (ProgramEncoding.encodeRecords dictionary)
    (Encoding.frame (clauseBytes C) ++ tail) [] [] output
  let v1 := {v0 with source := tail, capturedClause := (clauseBytes C).reverse}
  let v2 := {v1 with capturedClause := [], clause := clauseBytes C}
  let v3 := {v2 with clauseOutput := [false]}
  let v4 := {v3 with clause := [], clauseOutput := clauseResult dictionary C}
  obtain ⟨r1, h1⟩ := readClause_eval regs v0 (clauseBytes C) tail
  change Eval readClause _ (state regs v0) (state r1 v1) at h1
  have h2 := restoreClause_eval r1 v1 (clauseBytes C)
  change Eval restoreClause _ (state r1 v1) (state (readRegs r1 0 1 none) v2) at h2
  have h3 := seedClause_eval (readRegs r1 0 1 none) v2
  change Eval seedClause 2 (state (readRegs r1 0 1 none) v2)
    (state (Function.update (readRegs r1 0 1 none) 0 false) v3) at h3
  obtain ⟨nc, hnc, rc, hc⟩ := collectClause_eval dictionary C
    (Function.update (readRegs r1 0 1 none) 0 false) tail output
  change Eval collectClause nc (state (Function.update (readRegs r1 0 1 none) 0 false) v3)
    (state rc v4) at hc
  obtain ⟨rf, hf⟩ := emitClause_eval rc v4 (clauseResult dictionary C)
  refine ⟨_, ?_, rf, h1.seq (h2.seq (h3.seq (hc.seq hf)))⟩
  unfold clauseCost; omega

abbrev formulaTag : Cmd 8 22 := SubexpInputFrames.readTag 0

theorem formulaTag_eval (regs : Fin 8 → Bool) (dictionary tail output : Word) (flag : Bool) :
    ∃ rf, Eval formulaTag 1 (resting regs dictionary (flag :: tail) output)
      (resting rf dictionary tail output) ∧ rf 7 = flag := by
  obtain ⟨e, he, hs, hf⟩ := SubexpInputFrames.readTag_execute 0
    (resting regs dictionary (flag :: tail) output) flag tail rfl
  have heq : e = resting e.regs dictionary tail output := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · simpa only [resting, clauseState, baseView, state, update_source] using hs
  exact ⟨e.regs, by rw [heq] at he; exact he, hf⟩

def afterFormula : Formula → Word → Word
  | [], tail => tail
  | C :: rest, tail => Encoding.frame (clauseBytes C) ++ (encode rest ++ tail)

theorem formula_tag (F : Formula) (tail : Word) :
    encode F ++ tail = listFlag F :: afterFormula F tail := by
  cases F <;> simp [encode, Encoding.encodeList, listFlag, afterFormula, List.append_assoc]

abbrev formulaLoop : Cmd 8 22 := .while 7 (.seq clauseCommand formulaTag)

def formulaBudget (dictionary : List Word) : Formula → ℕ
  | [] => 0
  | C :: rest => clauseCost dictionary C + 2 + formulaBudget dictionary rest

theorem formulaLoop_eval (dictionary : List Word) (F : Formula) (regs : Fin 8 → Bool)
    (tail : Word) (acc : List (List ℕ)) (hg : regs 7 = listFlag F) :
    ∃ t ≤ formulaBudget dictionary F + 1, ∃ rf,
      Eval formulaLoop t
        (resting regs (ProgramEncoding.encodeRecords dictionary) (afterFormula F tail)
          (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) acc))
        (resting rf (ProgramEncoding.encodeRecords dictionary) tail
          (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) (formulaCodes dictionary F ++ acc))) := by
  induction F generalizing regs acc with
  | nil =>
      refine ⟨1, by simp [formulaBudget], regs, ?_⟩
      simpa only [afterFormula, formulaCodes, List.map_nil, List.reverse_nil, List.nil_append] using
        (Eval.while_false (body := .seq clauseCommand formulaTag)
          (a := resting regs (ProgramEncoding.encodeRecords dictionary) tail
            (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) acc)) hg)
  | cons C rest ih =>
      obtain ⟨nc, hnc, rc, hc⟩ := clause_eval dictionary C regs (encode rest ++ tail)
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) acc)
      change Eval clauseCommand nc _ (resting rc (ProgramEncoding.encodeRecords dictionary)
        (encode rest ++ tail) (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
          (clauseCodes dictionary C :: acc))) at hc
      obtain ⟨rt, ht, hrt⟩ := formulaTag_eval rc (ProgramEncoding.encodeRecords dictionary)
        (afterFormula rest tail) (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
          (clauseCodes dictionary C :: acc)) (listFlag rest)
      rw [← formula_tag] at ht
      obtain ⟨nl, hnl, rf, hl⟩ := ih rt (clauseCodes dictionary C :: acc) hrt
      refine ⟨nc + 1 + nl + 1, ?_, rf, ?_⟩
      · simp only [formulaBudget]; omega
      · have h := Eval.while_true (by exact hg) (hc.seq ht) hl
        simpa only [formulaLoop, afterFormula, formulaCodes, List.map_cons,
          List.reverse_cons, List.append_assoc, List.singleton_append] using h

abbrev seed : Cmd 8 22 := TupleProgram.pushConst 8 0 false

theorem seed_eval (regs : Fin 8 → Bool) (dictionary source : Word) :
    Eval seed 2 (resting regs dictionary source [])
      (resting (Function.update regs 0 false) dictionary source [false]) := by
  simpa only [resting, clauseState, baseView, state, TupleProgram.pushedState,
    store_output, update_output] using
    TupleProgram.pushConst_eval (8 : Fin 22) (0 : Fin 8) false (resting regs dictionary source [])

abbrev command : Cmd 8 22 := .seq seed (.seq formulaTag formulaLoop)
def program := compiled command (0 : Fin 22) 8

theorem program_runsIn (regs : Fin 8 → Bool) (dictionary : List Word) (F : Formula) :
    ∃ rf, RunsIn program (formulaBudget dictionary F + 5)
      ((resting regs (ProgramEncoding.encodeRecords dictionary) (encode F) []).withPC (some program.entry))
      ((resting rf (ProgramEncoding.encodeRecords dictionary) []
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) (formulaCodes dictionary F))).withPC none) := by
  have hs := seed_eval regs (ProgramEncoding.encodeRecords dictionary) (encode F)
  obtain ⟨rt, ht, hrt⟩ := formulaTag_eval (Function.update regs 0 false)
    (ProgramEncoding.encodeRecords dictionary) (afterFormula F []) [false] (listFlag F)
  rw [← formula_tag, List.append_nil] at ht
  obtain ⟨nl, hnl, rf, hl⟩ := formulaLoop_eval dictionary F rt [] [] hrt
  simp only [List.append_nil] at hl
  exact ⟨rf, 2 + (1 + nl) + 1, by omega, compiled_halt_trace (hs.seq (ht.seq hl)) 0 8⟩

@[simp] theorem formulaCodes_dictionary (F : Formula) :
    formulaCodes (RawIdEncoding.dictionary F) F = RawIdRenaming.physicalCodes F := by
  simp only [formulaCodes, RawIdRenaming.physicalCodes, RawIdRenaming.denseCodes,
    List.map_map, Function.comp_def ]
  rfl

theorem renamed_run (regs : Fin 8 → Bool) (F : Formula) :
    ∃ rf, RunsIn program (formulaBudget (RawIdEncoding.dictionary F) F + 5)
      ((resting regs (ProgramEncoding.encodeRecords (RawIdEncoding.dictionary F))
        (encode F) []).withPC (some program.entry))
      ((resting rf (ProgramEncoding.encodeRecords (RawIdEncoding.dictionary F)) []
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) (RawIdRenaming.physicalCodes F))).withPC none) := by
  simpa only [formulaCodes_dictionary] using program_runsIn regs (RawIdEncoding.dictionary F) F

end SubexponentialSAT.Subexp.RawIdRenameProgram

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecClauseLookupProgram
import OAI.Algorithms.SubexponentialSAT.RecordPrograms

namespace OAI.Algorithms

/-!
# Building a selected family from binary index records

The fixed program copies an encoded index tuple, parses its records, and calls
the actual binary-indexed record lookup. Source formula and original tuple are
preserved. Selected records are prepended, so output order is reversed. Invalid
indices contribute no record; the range guard used by the splitter rules them
out. All bounds are independent of the accumulated output suffix length.
-/

namespace SubexponentialSAT.ExecSelectedFamilyProgram

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 4 10
abbrev encode := ExecClauseLookupProgram.encode

def ports : RecordPrograms.Ports 4 10 where
  tag := 0
  present := 1
  found := 2
  source := 8
  payload := 9
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def lookupPort : Fin 7 → Fin 10 := Fin.castAdd 3

theorem lookupPort_injective : Function.Injective lookupPort := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 10 => x.val) h)

abbrev lookup : Cmd 4 10 :=
  .call (ProgramLinking.liftProgram ExecClauseLookupProgram.program id lookupPort)

def stage (v p go found : Bool)
    (source index output rest counter tuple tail payload : List Bool) : Data :=
  ⟨![v, p, go, found], ![source, index, output, rest, counter, [], [], tuple, tail, payload]⟩

def baseState (source tuple output : List Bool) : Data :=
  stage false false false false source [] output [] [] tuple [] []

theorem embed_stage (v p go found v' p' go' found' : Bool)
    (source index output rest counter source' index' output' rest' counter' tuple tail payload : List Bool) :
    embedState id lookupPort
      (stage v p go found source index output rest counter tuple tail payload)
      (ExecClauseLookupProgram.data v' p' go' found' source' index' output' rest' counter') =
      stage v' p' go' found' source' index' output' rest' counter' tuple tail payload := by
  apply ExecClauseLookupProgram.embed_eq _ _ Function.injective_id lookupPort_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;>
      simp_all [lookupPort, stage, Fin.exists_fin_succ ]

theorem lookup_eval (v p go found : Bool) (records : List (List Bool))
    (index output tuple tail payload : List Bool) :
    Eval lookup (ExecClauseLookupProgram.cost records index + 1)
      (stage v p go found (encode records) index output [] [] tuple tail payload)
      (stage false false false (records[CounterPrograms.value index]?).isSome
        (encode records) index
        (ExecClauseLookupProgram.prependResult (records[CounterPrograms.value index]?) output) [] [] tuple tail payload) := by
  have he := eval_call_lifted ExecClauseLookupProgram.program id lookupPort
    (stage v p go found (encode records) index output [] [] tuple tail payload)
    Function.injective_id lookupPort_injective
    (ExecClauseLookupProgram.program_trace v p go found records index output)
  simpa only [lookup, embed_stage] using he

abbrev callback : Cmd 4 10 :=
  .seq (.call (StackRoutines.transferProgram 9 1 0 1))
    (.seq lookup (.seq (.call (StackRoutines.clearProgram 1 0 1))
      (.seq (RecordPrograms.atom (.set 3 false)) (RecordPrograms.atom (.set 1 true)))))

def callbackCost (records : List (List Bool)) (bits : List Bool) : ℕ :=
  ExecClauseLookupProgram.cost records bits + 5 * bits.length + 9

theorem callback_eval (records : List (List Bool)) (bits tuple tail output : List Bool) :
    Eval callback (callbackCost records bits)
      (RecordPrograms.state ports (baseState (encode records) tuple output)
        false true false tail bits.reverse)
      (RecordPrograms.state ports
        (baseState (encode records) tuple
          (ExecClauseLookupProgram.prependResult (records[CounterPrograms.value bits]?) output))
        false true false tail []) := by
  let a := RecordPrograms.state ports (baseState (encode records) tuple output)
    false true false tail bits.reverse
  let b := stage false false false false (encode records) bits output [] [] tuple tail []
  have ht : Eval (.call (StackRoutines.transferProgram 9 1 0 1)) (3 * bits.length + 3) a b := by
    have he : Eval (.call (StackRoutines.transferProgram 9 1 0 1)) (3 * bits.reverse.length + 3) a
        ⟨readRegs a.regs 0 1 none, StackRoutines.transferStacks 9 1 a.stacks⟩ :=
      Eval.call _ (by simpa [a, ports, RecordPrograms.state, baseState, stage] using
        (ListRegisterProgram.transfer_run (r := 4) (s := 10) 9 1 0 1
          (by decide) (by decide) a.regs a.stacks))
    convert he using 1
    · simp
    · apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;>
        simp [a, ports, RecordPrograms.state, baseState, stage, readRegs,
          StackRoutines.transferStacks]
  have hl := lookup_eval false false false false records bits output tuple tail []
  let c := stage false false false (records[CounterPrograms.value bits]?).isSome
    (encode records) bits
    (ExecClauseLookupProgram.prependResult (records[CounterPrograms.value bits]?) output) [] [] tuple tail []
  let d := stage false false false (records[CounterPrograms.value bits]?).isSome
    (encode records) []
    (ExecClauseLookupProgram.prependResult (records[CounterPrograms.value bits]?) output) [] [] tuple tail []
  have hc : Eval (.call (StackRoutines.clearProgram 1 0 1)) (2 * bits.length + 3) c d := by
    have he : Eval (.call (StackRoutines.clearProgram 1 0 1)) (2 * bits.length + 3) c
        ⟨readRegs c.regs 0 1 none, StackRoutines.clearStacks 1 c.stacks⟩ :=
      Eval.call _ (by simpa [c, stage] using
        (ListRegisterProgram.clear_run (r := 4) (s := 10) 1 0 1 c.regs c.stacks))
    convert he using 1
    apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;>
      simp [c, stage, readRegs, StackRoutines.clearStacks]
  have hf := Eval.base (StructuredProgram.Eval.atom (.set (r := 4) (s := 10) 3 false) d)
  have hp := Eval.base (StructuredProgram.Eval.atom (.set (r := 4) (s := 10) 1 true)
    ((StructuredProgram.Atom.set 3 false).eval d))
  have he := ht.seq (hl.seq (hc.seq (hf.seq hp)))
  convert he using 1
  · simp [callbackCost]; omega
  · apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;>
      simp [d, ports, baseState, stage, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]

def selected (records words : List (List Bool)) : List (List Bool) :=
  words.filterMap (fun bits => records[CounterPrograms.value bits]?)

def prependRecords (records : List (List Bool)) (output : List Bool) : List Bool :=
  records.flatMap ExecClauseLookupProgram.record ++ output

theorem prepend_fold (records words : List (List Bool)) (output : List Bool) :
    words.foldl (fun acc bits => ExecClauseLookupProgram.prependResult (records[CounterPrograms.value bits]?) acc) output =
      prependRecords (selected records words).reverse output := by
  induction words generalizing output with
  | nil => simp [selected, prependRecords]
  | cons bits words ih =>
      cases h : records[CounterPrograms.value bits]? with
      | none =>
          simpa [List.foldl_cons, selected, h, ExecClauseLookupProgram.prependResult, prependRecords]
            using ih output
      | some row =>
          simpa [List.foldl_cons, selected, h, ExecClauseLookupProgram.prependResult, prependRecords,
            List.flatMap_append, List.append_assoc]
            using ih (ExecClauseLookupProgram.record row ++ output)

def invariant (records : List (List Bool)) (tuple : List Bool) (a : Data) : Prop :=
  ∃ output, a = baseState (encode records) tuple output

def effect (records : List (List Bool)) (bits : List Bool) (a b : Data) : Prop :=
  b.stacks 2 = ExecClauseLookupProgram.prependResult (records[CounterPrograms.value bits]?) (a.stacks 2)

theorem callback_contract (records : List (List Bool)) (tuple : List Bool) :
    RecordPrograms.CallbackContractWith ports callback (fun _ => false)
      (callbackCost records) (invariant records tuple) (effect records) := by
  intro bits tail base hinv
  obtain ⟨output, rfl⟩ := hinv
  refine ⟨callbackCost records bits,
    baseState (encode records) tuple
      (ExecClauseLookupProgram.prependResult (records[CounterPrograms.value bits]?) output),
    le_rfl, ⟨_, rfl⟩, ?_, callback_eval records bits tuple tail output⟩
  simp [effect, baseState, stage]

abbrev copyTuple : Cmd 4 10 := .call (StackRoutines.copyProgram 7 8 5 0 1)

abbrev command : Cmd 4 10 :=
  .seq copyTuple (.seq (RecordPrograms.iterate ports callback) (RecordPrograms.atom (.set 1 false)))

def program := compiled command 7 2

theorem copyTuple_eval (source tuple output : List Bool) :
    Eval copyTuple (7 * tuple.length + 5) (baseState source tuple output)
      (RecordPrograms.state ports (baseState source tuple output) false false false tuple []) := by
  let a := baseState source tuple output
  have he : Eval copyTuple (7 * tuple.length + 5) a
      ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks 7 8 a.stacks⟩ :=
    Eval.call _ (by simpa [a, baseState, stage] using
      (ListRegisterProgram.copy_run (r := 4) (s := 10) 7 8 5 0 1
        (by decide) (by decide) (by decide) (by decide) a.regs a.stacks rfl))
  convert he using 1
  apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;>
    simp [a, ports, baseState, stage, readRegs, StackRoutines.copyStacks]

private theorem unread_false (records : List (List Bool)) (suffix : List Bool) :
    RecordPrograms.unread (fun _ => false) records suffix = suffix := by
  induction records with
  | nil => rfl
  | cons bits rest ih => simpa only [RecordPrograms.unread, Bool.false_eq_true, ite_false] using ih

private theorem any_false (records : List (List Bool)) :
    records.any (fun _ => false) = false := by
  induction records with
  | nil => rfl
  | cons bits rest ih => exact ih

def traceCost (records words : List (List Bool)) : ℕ :=
  7 * (encode words).length + 10 + RecordPrograms.budget (callbackCost records) words

/-- Every callback is the concrete lookup program. The theorem is total even
for out-of-range indices; their absent results are removed by `filterMap`. -/
theorem command_eval (records words : List (List Bool)) (output : List Bool) :
    ∃ n, n + 1 ≤ traceCost records words ∧
      Eval command n (baseState (encode records) (encode words) output)
        (baseState (encode records) (encode words) (prependRecords (selected records words).reverse output)) := by
  obtain ⟨n, next, hn, hnext, history, run⟩ := RecordPrograms.iterate_run_with
    ports callback (fun _ => false) (callbackCost records) (invariant records (encode words))
    (effect records) (callback_contract records (encode words)) words []
    (baseState (encode records) (encode words) output) ⟨output, rfl⟩ false false false
  obtain ⟨acc, rfl⟩ := hnext
  have hacc : acc = prependRecords (selected records words).reverse output := by
    have hh := history.fold_of_false (fun _ _ => rfl)
      (fun s => s.stacks 2)
      (fun acc bits => ExecClauseLookupProgram.prependResult (records[CounterPrograms.value bits]?) acc)
      (fun _ _ _ h => h)
    simpa [baseState, stage, prepend_fold] using hh
  subst acc
  have hr : Eval (RecordPrograms.iterate ports callback) n
      (RecordPrograms.state ports (baseState (encode records) (encode words) output)
        false false false (encode words) [])
      (RecordPrograms.state ports
        (baseState (encode records) (encode words) (prependRecords (selected records words).reverse output))
        false true false [] []) := by
    simpa [encode, unread_false, any_false] using run
  have hc := copyTuple_eval (encode records) (encode words) output
  have hf : Eval (RecordPrograms.atom (.set (r := 4) (s := 10) 1 false)) 1
      (RecordPrograms.state ports
        (baseState (encode records) (encode words) (prependRecords (selected records words).reverse output))
        false true false [] [])
      (baseState (encode records) (encode words) (prependRecords (selected records words).reverse output)) := by
    have he := Eval.base (StructuredProgram.Eval.atom (.set (r := 4) (s := 10) 1 false)
      (RecordPrograms.state ports
        (baseState (encode records) (encode words) (prependRecords (selected records words).reverse output))
        false true false [] []))
    convert he using 1
    apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;>
      simp [ports, RecordPrograms.state, baseState, stage,
        StructuredProgram.Atom.instr, execInstr]
  refine ⟨(7 * (encode words).length + 5) + (n + 1), ?_, hc.seq (hr.seq hf)⟩
  unfold traceCost
  omega

theorem callbackCost_le (records : List (List Bool)) (bits : List Bool) :
    callbackCost records bits ≤ 80 * ((encode records).length + 1) * (bits.length + 1) := by
  have hc := ExecClauseLookupProgram.cost_le records bits
  unfold callbackCost
  nlinarith [Nat.zero_le ((encode records).length * bits.length)]

theorem budget_le (records words : List (List Bool)) :
    RecordPrograms.budget (callbackCost records) words ≤
      100 * ((encode records).length + 1) * (encode words).length := by
  induction words with
  | nil => simp [RecordPrograms.budget]
  | cons bits words ih =>
      have hc := callbackCost_le records bits
      simp only [RecordPrograms.budget, encode, Encoding.length_encodeList_cons, id_eq]
      change RecordPrograms.budget (callbackCost records) words ≤
        100 * ((encode records).length + 1) * (encode words).length at ih
      nlinarith [Nat.zero_le ((encode records).length * bits.length)]

/-- Local polynomial cost: accumulated output is never traversed or copied. -/
theorem traceCost_le (records words : List (List Bool)) :
    traceCost records words ≤
      128 * ((encode records).length + 1) * ((encode words).length + 1) := by
  have hb := budget_le records words
  unfold traceCost
  nlinarith [Nat.zero_le ((encode records).length * (encode words).length)]

theorem program_runs (records words : List (List Bool)) (output : List Bool) :
    RunsIn program (128 * ((encode records).length + 1) * ((encode words).length + 1))
      ((baseState (encode records) (encode words) output).withPC (some program.entry))
      ((baseState (encode records) (encode words)
        (prependRecords (selected records words).reverse output)).withPC none) := by
  obtain ⟨n, hn, he⟩ := command_eval records words output
  exact ⟨n + 1, hn.trans (traceCost_le records words), compiled_halt_trace he 7 2⟩

theorem prefix_encode (xs ys : List (List Bool)) :
    prependRecords xs (encode ys) = encode (xs ++ ys) := by
  induction xs with
  | nil => simp [prependRecords]
  | cons x xs ih =>
      simpa [prependRecords, encode, Encoding.encodeList, ExecClauseLookupProgram.record,
        ExecWorklistProgram.record, List.flatMap_cons, List.append_assoc] using
        congrArg (fun tail => ExecClauseLookupProgram.record x ++ tail) ih

theorem empty_output_runs (records words : List (List Bool)) :
    RunsIn program (128 * ((encode records).length + 1) * ((encode words).length + 1))
      ((baseState (encode records) (encode words) [false]).withPC (some program.entry))
      ((baseState (encode records) (encode words)
        (encode (selected records words).reverse)).withPC none) := by
  simpa only [← show encode [] = [false] from rfl, prefix_encode, List.append_nil] using
    program_runs records words [false]

theorem program_primitive (records words : List (List Bool)) (output : List Bool) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program *
        (128 * ((encode records).length + 1) * ((encode words).length + 1)))
      (BitProgram.primitiveCfg program
        ((baseState (encode records) (encode words) output).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((baseState (encode records) (encode words)
          (prependRecords (selected records words).reverse output)).withPC none)) := by
  obtain ⟨n, hn, ht⟩ := program_runs records words output
  exact (BitProgram.primitive_trace program ht).mono (Nat.mul_le_mul_left _ hn)

theorem selected_length_of_valid (records words : List (List Bool))
    (hvalid : ∀ bits ∈ words, CounterPrograms.value bits < records.length) :
    (selected records words).length = words.length := by
  induction words with
  | nil => simp [selected]
  | cons bits words ih =>
      have hv := hvalid bits (by simp)
      have ht := ih (fun word hw => hvalid word (by simp [hw]))
      have hs : records[CounterPrograms.value bits]? = some records[CounterPrograms.value bits] := by
        simp [hv]
      simpa [selected, hs] using congrArg Nat.succ ht

def selectedClauses (formula : List (List (List Bool))) (words : List (List Bool)) :
    List (List (List Bool)) := words.filterMap (fun bits => formula[CounterPrograms.value bits]?)

theorem selected_clause_records (formula : List (List (List Bool))) (words : List (List Bool)) :
    selected (formula.map encode) words = (selectedClauses formula words).map encode := by
  induction words with
  | nil => simp [selected, selectedClauses]
  | cons bits words ih =>
      cases h : formula[CounterPrograms.value bits]? <;>
        simp [selected, selectedClauses, List.getElem?_map, h] at ih ⊢ <;> exact ih

/-- Direct nested-CNF endpoint used by the splitter. The first emitted clause
comes from the last valid index in the tuple, because records are prepended. -/
theorem clause_family_runs (formula : List (List (List Bool))) (words : List (List Bool)) :
    RunsIn program
      (128 * ((Encoding.encodeList encode formula).length + 1) * ((encode words).length + 1))
      ((baseState (Encoding.encodeList encode formula) (encode words) [false]).withPC
        (some program.entry))
      ((baseState (Encoding.encodeList encode formula) (encode words)
        (Encoding.encodeList encode (selectedClauses formula words).reverse)).withPC none) := by
  simpa only [selected_clause_records, ← List.map_reverse, ExecClauseLookupProgram.encode_map] using
    empty_output_runs (formula.map encode) words

end SubexponentialSAT.ExecSelectedFamilyProgram

end OAI.Algorithms

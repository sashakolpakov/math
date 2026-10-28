import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.SelectorProgram

namespace OAI.Algorithms

/-! The output boundary for the fixed first-match selector. A matching payload
is parsed onto the output port; an absent key copies the original query. -/

namespace SubexponentialSAT.Subexp.SelectorProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

abbrev materialize : Cmd 5 6 :=
  .ite 4 (.call (parseFrame 5 1))
    (.call (StackRoutines.copyProgram 2 1 4 (0 : Fin 5) 1))

def materializeBudget (query : List Bool) : Option (List Bool) → ℕ
  | none => 7 * query.length + 6
  | some value => 6 * value.length + 5

theorem materialize_eval (query : List Bool) (result : Option (List Bool))
    (regs : Fin 5 → Bool) (tail : List Bool) (hflag : regs 4 = result.isSome) :
    ∃ regs', Eval materialize (materializeBudget query result)
      (recordState regs tail [] query.reverse [] [] (framedResult result))
      (recordState regs' tail (result.getD query).reverse query.reverse [] [] []) := by
  cases result with
  | none =>
      let d := recordState regs tail [] query.reverse [] [] []
      have hc := copy_eval d 2 1 4 (by decide) (by decide) (by decide) (by rfl)
      have hc' : Eval (.call (StackRoutines.copyProgram 2 1 4 (0 : Fin 5) 1))
          (7 * query.length + 5) d
          (recordState (readRegs regs 0 1 none) tail query.reverse query.reverse [] [] []) := by
        simpa [d, afterCopy, StackRoutines.copyStacks, recordState] using hc
      refine ⟨readRegs regs 0 1 none, ?_⟩
      simpa [materialize, materializeBudget, framedResult, d, Nat.add_assoc] using
        (Eval.ite_false (by simpa [d, recordState] using hflag) hc')
  | some value =>
      let d := recordState regs tail [] query.reverse [] [] (Encoding.frame value)
      have hp := parseFrame_eval d 5 1 (by decide) value [] (by simp [d ])
      have hp' : Eval (.call (parseFrame 5 1)) (6 * value.length + 4) d
          (recordState (readRegs regs 0 1 (some false)) tail value.reverse query.reverse [] [] []) := by
        simpa [d, afterFrame, recordState] using hp
      refine ⟨readRegs regs 0 1 (some false), ?_⟩
      simpa [materialize, materializeBudget, framedResult, d, Nat.add_assoc] using
        (Eval.ite_true (by simpa [d, recordState] using hflag) hp')

abbrev command : Cmd 5 6 :=
  .seq (atom (.set 4 false)) (.seq peek (.seq scan materialize))

abbrev program : Program 5 6 (size command + 1) := compiled command 0 1

theorem program_control_size : size command + 1 = 82 := by decide

def budget (query : List Bool) (records : List (List Bool × List Bool)) : ℕ :=
  scanBudget query records + materializeBudget query (records.lookup query) + 3

/-- The full selector executes only the existing finite parser, equality,
copy, and Boolean control instructions. -/
theorem command_eval (query : List Bool) (records : List (List Bool × List Bool))
    (regs : Fin 5 → Bool) :
    ∃ n ≤ budget query records - 1, ∃ regs' tail,
      Eval command n
        (recordState regs (rawRecords records) [] query.reverse [] [] [])
        (recordState regs' tail ((records.lookup query).getD query).reverse
          query.reverse [] [] []) := by
  let reset := Function.update regs 4 false
  have hset : Eval (atom (.set 4 false)) 1
      (recordState regs (rawRecords records) [] query.reverse [] [] [])
      (recordState reset (rawRecords records) [] query.reverse [] [] []) := by
    simpa [atom, reset, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, recordState]
      using (Eval.base (StructuredProgram.Eval.atom
        (StructuredProgram.Atom.set (4 : Fin 5) false)
        (recordState regs (rawRecords records) [] query.reverse [] [] [])))
  have hpeek : Eval peek 1
      (recordState reset (rawRecords records) [] query.reverse [] [] [])
      (ready reset records query) := peek_eval reset _ _ _
  obtain ⟨ns, hns, middle, tail, hs, hflag⟩ := scan_eval query records reset (by simp [reset])
  obtain ⟨final, hf⟩ := materialize_eval query (records.lookup query) middle tail hflag
  refine ⟨1 + (1 + (ns + materializeBudget query (records.lookup query))), ?_,
    final, tail, Eval.seq hset (Eval.seq hpeek (Eval.seq hs hf))⟩
  dsimp [budget]
  omega

theorem program_trace (query : List Bool) (records : List (List Bool × List Bool))
    (regs : Fin 5 → Bool) :
    ∃ n ≤ budget query records, ∃ regs' tail,
      Trace program n
        ((recordState regs (rawRecords records) [] query.reverse [] [] []).withPC
          (some program.entry))
        ((recordState regs' tail ((records.lookup query).getD query).reverse
          query.reverse [] [] []).withPC none) := by
  obtain ⟨n, hn, regs', tail, ht⟩ := command_eval query records regs
  refine ⟨n + 1, ?_, regs', tail, compiled_halt_trace ht 0 1⟩
  have hb : 0 < budget query records := by dsimp [budget]; omega
  omega

theorem program_primitive (query : List Bool) (records : List (List Bool × List Bool))
    (regs : Fin 5 → Bool) :
    ∃ regs' tail,
      SubexponentialSAT.Computation.RunsIn (BitProgram.primitive program).step
        (primitiveOverhead program * budget query records)
        (primitiveCfg program
          ((recordState regs (rawRecords records) [] query.reverse [] [] []).withPC
            (some program.entry)))
        (primitiveCfg program
          ((recordState regs' tail ((records.lookup query).getD query).reverse
            query.reverse [] [] []).withPC none)) := by
  obtain ⟨n, hn, regs', tail, ht⟩ := program_trace query records regs
  exact ⟨regs', tail, BitProgram.primitive_execution program ⟨n, hn, ht⟩⟩

end SubexponentialSAT.Subexp.SelectorProgram

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.SelectorMapProgram

namespace OAI.Algorithms

/-!+# Selecting and framing both read plans of a vertex pair

The two selector-map calls share a persistent table. Stack 6 initially holds
the left query records and stack 9 the right query records. Stack 11 is an
existing record accumulator. The result prepends one record whose payload is
`frame leftPlanBytes ++ frame rightPlanBytes`.
-/

namespace SubexponentialSAT.Subexp.SelectorPairProgram

open BitProgram StructuredCalls

abbrev Data := State 8 12

def state (regs : Fin 8 → Bool) (queries table output right saved acc : List Bool) : Data :=
  ⟨regs, ![[], [], [], [], [], [], queries, table, output, right, saved, acc]⟩

def stackMap : Fin 9 → Fin 12 := Fin.castAdd 3

theorem stackMap_injective : Function.Injective stackMap := by
  intro a b h
  exact Fin.ext (congrArg (fun x : Fin 12 => x.val) h)

abbrev mapProgram : Program 8 12 (size SelectorMapProgram.command + 1) :=
  ProgramLinking.liftProgram SelectorMapProgram.program id stackMap

def planBytes (records : List (List Bool × List Bool)) (queries : List (List Bool)) : List Bool :=
  ProgramEncoding.encodeRecords (SelectorMapProgram.mappedRecords records queries)

def payload (left right : List Bool) : List Bool :=
  Encoding.frame left ++ Encoding.frame right

def rightPorts : RecordPrograms.Ports 8 12 :=
  ⟨0, 1, 2, 9, 8, by decide, by decide, by decide, by decide⟩

def leftPorts : RecordPrograms.Ports 8 12 :=
  ⟨0, 1, 2, 10, 8, by decide, by decide, by decide, by decide⟩

def outputPorts : RecordPrograms.Ports 8 12 :=
  ⟨0, 1, 2, 10, 11, by decide, by decide, by decide, by decide⟩

abbrev prepareRight : Cmd 8 12 :=
  .seq (.call (StackRoutines.transferProgram 8 10 (0 : Fin 8) 1))
    (.seq (.call (StackRoutines.copyProgram 9 6 4 (0 : Fin 8) 1))
      (.call (StackRoutines.clearProgram 9 (0 : Fin 8) 1)))

abbrev buildPayload : Cmd 8 12 :=
  .seq (.call (StackRoutines.transferProgram 8 9 (0 : Fin 8) 1))
    (.seq (TupleProgram.pushConst 8 0 false)
      (.seq (TupleProgram.escape rightPorts)
        (.seq (TupleProgram.pushConst 8 0 false)
          (TupleProgram.escape leftPorts))))

abbrev emitPayload : Cmd 8 12 :=
  .seq (.call (StackRoutines.transferProgram 8 10 (0 : Fin 8) 1))
    (.seq (TupleProgram.pushConst 11 0 false)
      (.seq (TupleProgram.escape outputPorts) (TupleProgram.pushConst 11 0 true)))

abbrev framePair : Cmd 8 12 := .seq buildPayload emitPayload

abbrev command : Cmd 8 12 :=
  .seq (.call mapProgram) (.seq prepareRight (.seq (.call mapProgram) framePair))

abbrev program : Program 8 12 (size command + 1) := compiled command 6 11

theorem map_eval (records : List (List Bool × List Bool)) (queries : List (List Bool))
    (regs : Fin 8 → Bool) (right saved acc : List Bool) :
    ∃ n ≤ SelectorMapProgram.budget records queries, ∃ regs',
      Eval (.call mapProgram) n
        (state regs (ProgramEncoding.encodeRecords queries)
          (SelectorProgram.rawRecords records) [] right saved acc)
        (state regs' [] (SelectorProgram.rawRecords records)
          (planBytes records queries) right saved acc) := by
  obtain ⟨n, hn, regs', ht⟩ := SelectorMapProgram.program_trace_from records queries regs
  let a := state regs (ProgramEncoding.encodeRecords queries)
    (SelectorProgram.rawRecords records) [] right saved acc
  let b := state regs' [] (SelectorProgram.rawRecords records)
    (planBytes records queries) right saved acc
  have ha : embedState id stackMap a
      (SelectorMapProgram.inputStateWith regs records queries) = a := by
    apply SelectorMapProgram.embed_eq _ _ Function.injective_id stackMap_injective
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j hj; rfl
  have hb : embedState id stackMap a
      (SelectorMapProgram.outputState records queries regs') = b := by
    apply SelectorMapProgram.embed_eq _ _ Function.injective_id stackMap_injective
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j hj
      fin_cases j <;>
        simp_all [stackMap, state, a, b, Fin.exists_fin_succ]
  refine ⟨n, hn, regs', ?_⟩
  have h := eval_call_lifted SelectorMapProgram.program id stackMap a
    Function.injective_id stackMap_injective ht
  simpa only [mapProgram, ha, hb, a, b] using h

theorem prepareRight_eval (regs : Fin 8 → Bool) (table left right acc : List Bool) :
    ∃ regs', Eval prepareRight (3 * left.length + 9 * right.length + 11)
      (state regs [] table left right [] acc)
      (state regs' right table [] [] left.reverse acc) := by
  let a := state regs [] table left right [] acc
  let b : Data := ⟨readRegs a.regs 0 1 none, StackRoutines.transferStacks 8 10 a.stacks⟩
  let c : Data := ⟨readRegs b.regs 0 1 none, StackRoutines.copyStacks 9 6 b.stacks⟩
  let d : Data := ⟨readRegs c.regs 0 1 none, StackRoutines.clearStacks 9 c.stacks⟩
  have h1 := TupleProgram.transfer_eval (8 : Fin 12) 10 (0 : Fin 8) 1
    (by decide) (by decide) a
  have h2 := TupleProgram.copy_eval (9 : Fin 12) 6 4 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) b (by rfl)
  have h3 := TupleProgram.clear_eval (9 : Fin 12) (0 : Fin 8) 1 c
  have hd : d = state d.regs right table [] [] left.reverse acc := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;>
        simp [ c, b, a, state, StackRoutines.transferStacks,
          StackRoutines.copyStacks, StackRoutines.clearStacks]
  refine ⟨d.regs, ?_⟩
  rw [← hd]
  convert h1.seq (h2.seq h3) using 1 ;
    simp [ a, b, c, state, StackRoutines.transferStacks,
      StackRoutines.copyStacks] ; omega

def frameCost (left right : List Bool) : ℕ :=
  5 * left.length + 8 * right.length + 8 * (payload left right).length + 23

theorem buildPayload_eval (regs : Fin 8 → Bool) (table left right acc : List Bool) :
    ∃ regs', Eval buildPayload (5 * left.length + 8 * right.length + 13)
      (state regs [] table right [] left.reverse acc)
      (state regs' [] table (payload left right) [] [] acc) := by
  let a := state regs [] table right [] left.reverse acc
  let b : Data := ⟨readRegs a.regs 0 1 none, StackRoutines.transferStacks 8 9 a.stacks⟩
  let c := TupleProgram.pushedState 8 0 false b
  let d := TupleProgram.escapedState rightPorts c
  let e := TupleProgram.pushedState 8 0 false d
  let f := TupleProgram.escapedState leftPorts e
  have h1 := TupleProgram.transfer_eval (8 : Fin 12) 9 (0 : Fin 8) 1
    (by decide) (by decide) a
  have h2 := TupleProgram.pushConst_eval (8 : Fin 12) (0 : Fin 8) false b
  have h3 := TupleProgram.escape_eval_state rightPorts c
  have h4 := TupleProgram.pushConst_eval (8 : Fin 12) (0 : Fin 8) false d
  have h5 := TupleProgram.escape_eval_state leftPorts e
  have hf : f = state f.regs [] table (payload left right) [] [] acc := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext k
      fin_cases k <;>
        simp [ e, d, c, b, a, state, leftPorts, rightPorts,
          StackRoutines.transferStacks,
          payload, TupleProgram.frame_eq_escaped, List.append_assoc]
  refine ⟨f.regs, ?_⟩
  rw [← hf]
  convert h1.seq (h2.seq (h3.seq (h4.seq h5))) using 1 ;
    simp [ e, d, c, b, a, state, leftPorts, rightPorts,
      StackRoutines.transferStacks ] ; omega

theorem emitPayload_eval (regs : Fin 8 → Bool) (table bits acc : List Bool) :
    ∃ regs', Eval emitPayload (8 * bits.length + 10)
      (state regs [] table bits [] [] acc)
      (state regs' [] table [] [] [] (TupleProgram.prependRecord bits acc)) := by
  let a := state regs [] table bits [] [] acc
  let b : Data := ⟨readRegs a.regs 0 1 none, StackRoutines.transferStacks 8 10 a.stacks⟩
  let c := TupleProgram.pushedState 11 0 false b
  let d := TupleProgram.escapedState outputPorts c
  let e := TupleProgram.pushedState 11 0 true d
  have h1 := TupleProgram.transfer_eval (8 : Fin 12) 10 (0 : Fin 8) 1
    (by decide) (by decide) a
  have h2 := TupleProgram.pushConst_eval (11 : Fin 12) (0 : Fin 8) false b
  have h3 := TupleProgram.escape_eval_state outputPorts c
  have h4 := TupleProgram.pushConst_eval (11 : Fin 12) (0 : Fin 8) true d
  have he : e = state e.regs [] table [] [] [] (TupleProgram.prependRecord bits acc) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;>
        simp [ d, c, b, a, state, outputPorts, StackRoutines.transferStacks, TupleProgram.prependRecord,
          TupleProgram.frame_eq_escaped, List.append_assoc]
  refine ⟨e.regs, ?_⟩
  rw [← he]
  convert h1.seq (h2.seq (h3.seq h4)) using 1 ;
    simp [ c, b, a, state, outputPorts, StackRoutines.transferStacks
      ] ; omega

theorem framePair_eval (regs : Fin 8 → Bool) (table left right acc : List Bool) :
    ∃ regs', Eval framePair (frameCost left right)
      (state regs [] table right [] left.reverse acc)
      (state regs' [] table [] [] [] (TupleProgram.prependRecord (payload left right) acc)) := by
  obtain ⟨r1, h1⟩ := buildPayload_eval regs table left right acc
  obtain ⟨r2, h2⟩ := emitPayload_eval r1 table (payload left right) acc
  refine ⟨r2, ?_⟩
  convert h1.seq h2 using 1 ; simp [ frameCost] ; omega

def cost (records : List (List Bool × List Bool)) (left right : List (List Bool)) : ℕ :=
  SelectorMapProgram.budget records left + SelectorMapProgram.budget records right +
    3 * (planBytes records left).length + 9 * (ProgramEncoding.encodeRecords right).length +
      11 + frameCost (planBytes records left) (planBytes records right) + 1

/-- Both selections, all moves, and both framing layers are actual fixed
instructions. No preparation operation is hidden in a callback contract. -/
theorem program_trace (records : List (List Bool × List Bool))
    (left right : List (List Bool)) (regs : Fin 8 → Bool) (acc : List Bool) :
    ∃ n ≤ cost records left right, ∃ regs',
      Trace program n
        ((state regs (ProgramEncoding.encodeRecords left) (SelectorProgram.rawRecords records)
          [] (ProgramEncoding.encodeRecords right) [] acc).withPC (some program.entry))
        ((state regs' [] (SelectorProgram.rawRecords records) [] [] []
          (TupleProgram.prependRecord
            (payload (planBytes records left) (planBytes records right)) acc)).withPC none) := by
  obtain ⟨nl, hnl, r1, h1⟩ := map_eval records left regs
    (ProgramEncoding.encodeRecords right) [] acc
  obtain ⟨r2, h2⟩ := prepareRight_eval r1 (SelectorProgram.rawRecords records)
    (planBytes records left) (ProgramEncoding.encodeRecords right) acc
  obtain ⟨nr, hnr, r3, h3⟩ := map_eval records right r2 [] (planBytes records left).reverse acc
  obtain ⟨r4, h4⟩ := framePair_eval r3 (SelectorProgram.rawRecords records)
    (planBytes records left) (planBytes records right) acc
  have ht := compiled_halt_trace (h1.seq (h2.seq (h3.seq h4))) (6 : Fin 12) 11
  refine ⟨nl + (3 * (planBytes records left).length +
      9 * (ProgramEncoding.encodeRecords right).length + 11 +
        (nr + frameCost (planBytes records left) (planBytes records right))) + 1,
      by dsimp [cost]; omega, r4, ?_⟩
  exact ht

theorem program_primitive (records : List (List Bool × List Bool))
    (left right : List (List Bool)) (regs : Fin 8 → Bool) (acc : List Bool) :
    ∃ regs', Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * cost records left right)
      (BitProgram.primitiveCfg program
        ((state regs (ProgramEncoding.encodeRecords left) (SelectorProgram.rawRecords records)
          [] (ProgramEncoding.encodeRecords right) [] acc).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((state regs' [] (SelectorProgram.rawRecords records) [] [] []
          (TupleProgram.prependRecord
            (payload (planBytes records left) (planBytes records right)) acc)).withPC none)) := by
  obtain ⟨n, hn, regs', ht⟩ := program_trace records left right regs acc
  exact ⟨regs', BitProgram.primitive_execution program ⟨n, hn, ht⟩⟩

theorem planBytes_length_le (records : List (List Bool × List Bool))
    (queries : List (List Bool)) :
    (planBytes records queries).length ≤
      ((SelectorProgram.rawRecords records).length + 1) *
        (ProgramEncoding.encodeRecords queries).length := by
  have hsum : ((queries.map (SelectorMapProgram.selected records)).map List.length).sum ≤
      (queries.map List.length).sum + queries.length * (SelectorProgram.rawRecords records).length := by
    induction queries with
    | nil => simp
    | cons query queries ih =>
        have h := SelectorMapProgram.selected_length_le records query
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        nlinarith
  simp only [planBytes, SelectorMapProgram.mappedRecords, ProgramEncoding.encodeRecords_length,
    List.map_reverse, List.sum_reverse, List.length_reverse, List.length_map]
  nlinarith [Nat.zero_le ((SelectorProgram.rawRecords records).length *
    (queries.map List.length).sum)]

/-- Polynomial in the actual table and two query encodings, including the
copies and both levels of output escaping. -/
theorem cost_bound (records : List (List Bool × List Bool))
    (left right : List (List Bool)) :
    cost records left right ≤
      1100 * ((SelectorProgram.rawRecords records).length + 1) *
        ((ProgramEncoding.encodeRecords left).length +
          (ProgramEncoding.encodeRecords right).length + 1) := by
  have hl := SelectorMapProgram.budget_bound records left
  have hr := SelectorMapProgram.budget_bound records right
  have hpl := planBytes_length_le records left
  have hpr := planBytes_length_le records right
  simp only [cost, frameCost, payload, List.length_append, Encoding.length_frame]
  nlinarith [Nat.zero_le ((SelectorProgram.rawRecords records).length *
    (ProgramEncoding.encodeRecords left).length),
    Nat.zero_le ((SelectorProgram.rawRecords records).length *
      (ProgramEncoding.encodeRecords right).length)]

theorem program_primitive_polynomial (records : List (List Bool × List Bool))
    (left right : List (List Bool)) (regs : Fin 8 → Bool) (acc : List Bool) :
    ∃ regs', Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program *
        (1100 * ((SelectorProgram.rawRecords records).length + 1) *
          ((ProgramEncoding.encodeRecords left).length +
            (ProgramEncoding.encodeRecords right).length + 1)))
      (BitProgram.primitiveCfg program
        ((state regs (ProgramEncoding.encodeRecords left) (SelectorProgram.rawRecords records)
          [] (ProgramEncoding.encodeRecords right) [] acc).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((state regs' [] (SelectorProgram.rawRecords records) [] [] []
          (TupleProgram.prependRecord
            (payload (planBytes records left) (planBytes records right)) acc)).withPC none)) := by
  obtain ⟨n, hn, regs', ht⟩ := program_trace records left right regs acc
  exact ⟨regs', BitProgram.primitive_execution program
    ⟨n, hn.trans (cost_bound records left right), ht⟩⟩

theorem planBytes_selection (currentSize : ℕ) (remaining plan : List ℕ) :
    planBytes (SelectorProgram.selectionEntries currentSize remaining)
      (plan.reverse.map SelectorProgram.unaryIndex) =
    ProgramEncoding.encodeRecords (plan.map (fun n => SelectorProgram.unaryIndex
      (ReadPlan.selectPosition currentSize remaining n))) := by
  rw [planBytes, SelectorMapProgram.mappedRecords_selection]

/-- The exact pair payload expected by the collision-score record iterator. -/
theorem selected_pair_trace (currentSize : ℕ) (remaining left right : List ℕ)
    (regs : Fin 8 → Bool) (acc : List Bool) :
    ∃ n ≤ cost (SelectorProgram.selectionEntries currentSize remaining)
        (left.reverse.map SelectorProgram.unaryIndex) (right.reverse.map SelectorProgram.unaryIndex),
      ∃ regs', Trace program n
        ((state regs
          (ProgramEncoding.encodeRecords (left.reverse.map SelectorProgram.unaryIndex))
          (SelectorProgram.rawRecords (SelectorProgram.selectionEntries currentSize remaining)) []
          (ProgramEncoding.encodeRecords (right.reverse.map SelectorProgram.unaryIndex)) [] acc).withPC
          (some program.entry))
        ((state regs' []
          (SelectorProgram.rawRecords (SelectorProgram.selectionEntries currentSize remaining)) [] [] []
          (TupleProgram.prependRecord
            (Encoding.frame (ProgramEncoding.encodeRecords (left.map (fun n =>
              SelectorProgram.unaryIndex (ReadPlan.selectPosition currentSize remaining n)))) ++
             Encoding.frame (ProgramEncoding.encodeRecords (right.map (fun n =>
              SelectorProgram.unaryIndex (ReadPlan.selectPosition currentSize remaining n))))) acc)).withPC none) := by
  obtain ⟨n, hn, regs', ht⟩ := program_trace (SelectorProgram.selectionEntries currentSize remaining)
    (left.reverse.map SelectorProgram.unaryIndex) (right.reverse.map SelectorProgram.unaryIndex) regs acc
  exact ⟨n, hn, regs', by simpa only [payload, planBytes_selection] using ht⟩

end SubexponentialSAT.Subexp.SelectorPairProgram

end OAI.Algorithms

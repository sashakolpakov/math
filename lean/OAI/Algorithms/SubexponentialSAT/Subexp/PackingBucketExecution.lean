import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketFold

namespace OAI.Algorithms

/-! The actual all-type scan and minimum fold, preserving the supplied type order. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open BitProgram StructuredCalls MatrixProgramSupport PackingBucketCalls

def parserRegs (regs : Fin 8 → Bool) (tag present found : Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update regs 5 tag) 6 present) 7 found

theorem parser_state (regs : Fin 8 → Bool)
    (rows query bucket saved keys scan minimum table count result newKeys newQuery : List Bool)
    (tag present found : Bool) :
    RecordPrograms.state ports
      (state regs rows query bucket saved keys scan minimum table count result)
      tag present found newKeys newQuery =
    state (parserRegs regs tag present found) rows newQuery bucket saved newKeys scan
      minimum table count result := by
  apply MatrixProgramSupport.data_ext <;> try rfl
  funext i
  fin_cases i <;> simp [RecordPrograms.state, ports, state]

def invariant (records : List BucketProgram.Record) (a : Data) : Prop :=
  a = state a.regs [] (a.stacks 2) [] (BucketProgram.encodeRecords records.reverse)
    (a.stacks 7) [] (List.replicate (a.stacks 10).length true) (a.stacks 11) [] [] ∧
  (a.stacks 10).length ≤ records.length

def effect (records : List BucketProgram.Record) (query : List Bool) (a b : Data) : Prop :=
  (b.stacks 10).length = min (a.stacks 10).length (BucketProgram.selected records query).length ∧
  b.stacks 11 = afterBucket records query (a.stacks 11)

theorem invariant_state (records : List BucketProgram.Record) (regs : Fin 8 → Bool)
    (query keys acc : List Bool) (m : ℕ) (hm : m ≤ records.length) :
    invariant records (state regs [] query [] (BucketProgram.encodeRecords records.reverse)
      keys [] (List.replicate m true) acc [] []) := by
  constructor
  · simp [state]
  · simpa [state] using hm

theorem callback_contract (records : List BucketProgram.Record) :
    RecordPrograms.CallbackContractWith ports callback (fun _ => false)
      (callbackCost records) (invariant records) (effect records) := by
  intro query tail base hb
  obtain ⟨n, hn, rf, he⟩ := callback_eval records query tail (base.stacks 11)
    (base.stacks 10).length hb.2 (parserRegs base.regs false true false)
  let next := state (finishRegs rf) [] [] [] (BucketProgram.encodeRecords records.reverse)
    tail [] (List.replicate (min (base.stacks 10).length
      (BucketProgram.selected records query).length) true)
    (afterBucket records query (base.stacks 11)) [] []
  have hinput : RecordPrograms.state ports base false true false tail query.reverse =
      state (parserRegs base.regs false true false) [] query.reverse []
        (BucketProgram.encodeRecords records.reverse) tail []
        (List.replicate (base.stacks 10).length true) (base.stacks 11) [] [] := by
    calc
      _ = RecordPrograms.state ports
          (state base.regs [] (base.stacks 2) [] (BucketProgram.encodeRecords records.reverse)
            (base.stacks 7) [] (List.replicate (base.stacks 10).length true)
            (base.stacks 11) [] []) false true false tail query.reverse :=
        congrArg (fun a => RecordPrograms.state ports a false true false tail query.reverse) hb.1
      _ = _ := parser_state ..
  have houtput : RecordPrograms.state ports next false true false tail [] = next := by
    apply RecordPrograms.state_eq_self <;> simp [next, ports, state, finishRegs]
  refine ⟨n, next, hn, ?_, ?_, ?_⟩
  · exact invariant_state records (finishRegs rf) [] tail _ _
      ((min_le_left _ _).trans hb.2)
  · simp [effect, next, state]
  · rw [hinput, houtput]
    exact he

def recordPrefix (records : List BucketProgram.Record) (keys : List (List Bool)) : List Bool :=
  (table records keys).flatMap (fun bits => true :: Encoding.frame bits)

theorem encodeTable_eq_prefix (records : List BucketProgram.Record) (keys : List (List Bool)) :
    ProgramEncoding.encodeRecords (table records keys) = recordPrefix records keys ++ [false] := by
  exact SelectorMapProgram.encodeRecords_eq_prefix (table records keys)

theorem fold_afterBucket (records : List BucketProgram.Record) (keys : List (List Bool))
    (acc : List Bool) :
    keys.foldl (fun out key => afterBucket records key out) acc =
      (recordPrefix records keys).reverse ++ acc := by
  induction keys generalizing acc with
  | nil => rfl
  | cons key keys ih =>
    rw [List.foldl_cons, ih]
    simp [recordPrefix, table, afterBucket, List.reverse_append, List.append_assoc]

def inputState (records : List BucketProgram.Record) (keys : List (List Bool))
    (initial : ℕ) (suffix : List Bool) (regs : Fin 8 → Bool) : Data :=
  state regs [] [] [] (BucketProgram.encodeRecords records.reverse)
    (ProgramEncoding.encodeRecords keys ++ suffix) [] (List.replicate initial true) [] [] []

def outputState (records : List BucketProgram.Record) (keys : List (List Bool))
    (initial : ℕ) (suffix : List Bool) (regs : Fin 8 → Bool) : Data :=
  state regs [] [] (ProgramEncoding.encodeRecords (table records keys))
    (BucketProgram.encodeRecords records.reverse) suffix []
    (List.replicate (minimum records keys initial) true) [] [] []

/-- The real iterator calls the filter, frame counter and unary minimum routine
for every key. The output table has precisely the original key order. -/
theorem program_trace (records : List BucketProgram.Record) (keys : List (List Bool))
    (initial : ℕ) (hinitial : initial ≤ records.length) (suffix : List Bool)
    (regs : Fin 8 → Bool) :
    ∃ n ≤ budget records keys, ∃ rf,
      Trace program n
        ((inputState records keys initial suffix regs).withPC (some program.entry))
        ((outputState records keys initial suffix rf).withPC none) := by
  let a := inputState records keys initial suffix regs
  have ha : invariant records a := invariant_state records regs [] _ [] initial hinitial
  obtain ⟨n, next, hn, hnext, history, hiter⟩ :=
    RecordPrograms.iterate_run_with ports callback (fun _ => false) (callbackCost records)
      (invariant records) (effect records) (callback_contract records)
      keys suffix a ha (a.regs 5) (a.regs 6) (a.regs 7)
  have hstart : RecordPrograms.state ports a (a.regs 5) (a.regs 6) (a.regs 7)
      (Encoding.encodeList id keys ++ suffix) [] = a := by
    apply RecordPrograms.state_eq_self <;> simp [ports, a, inputState, state,
      ProgramEncoding.encodeRecords]
  have hminimum : (next.stacks 10).length = minimum records keys initial := by
    have h := history.fold_of_false (fun _ _ => rfl) (fun d => (d.stacks 10).length)
      (fun m key => min m (BucketProgram.selected records key).length)
      (fun _ _ _ h => h.1)
    simpa [minimum, a, inputState, state] using h
  have htable : next.stacks 11 = (recordPrefix records keys).reverse := by
    have h := history.fold_of_false (fun _ _ => rfl) (fun d => d.stacks 11)
      (fun acc key => afterBucket records key acc) (fun _ _ _ h => h.2)
    rw [fold_afterBucket] at h
    simpa [a, inputState, state] using h
  let b := state (parserRegs next.regs false true false) [] [] []
    (BucketProgram.encodeRecords records.reverse) suffix []
    (List.replicate (minimum records keys initial) true) (recordPrefix records keys).reverse [] []
  have hend : RecordPrograms.state ports next false true false suffix [] = b := by
    calc
      _ = RecordPrograms.state ports
          (state next.regs [] (next.stacks 2) [] (BucketProgram.encodeRecords records.reverse)
            (next.stacks 7) [] (List.replicate (next.stacks 10).length true)
            (next.stacks 11) [] []) false true false suffix [] :=
        congrArg (fun d => RecordPrograms.state ports d false true false suffix []) hnext.1
      _ = b := by rw [parser_state, hminimum, htable]
  have hiter' : Eval (RecordPrograms.iterate ports callback) n a b := by
    have hany : keys.any (fun _ => false) = false := by simp
    simpa only [hstart, hany, TupleProgram.unread_false, hend] using hiter
  let c := TupleProgram.pushedState (11 : Fin 15) (0 : Fin 8) false b
  have hpush := TupleProgram.pushConst_eval (11 : Fin 15) (0 : Fin 8) false b
  obtain ⟨d, htransfer, hd⟩ := transfer_eval (11 : Fin 15) 5 (by decide) c
  have houtput : d = outputState records keys initial suffix d.regs := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hd]
    funext i
    fin_cases i <;>
      simp [outputState, b, c, state,
        StackRoutines.transferStacks, List.reverse_cons, encodeTable_eq_prefix]
  have hlength : (c.stacks 11).length =
      (ProgramEncoding.encodeRecords (table records keys)).length := by
    simp [c, b, state, encodeTable_eq_prefix]
  have hrun := compiled_halt_trace (hiter'.seq (hpush.seq htransfer)) (7 : Fin 15) 5
  refine ⟨n + (2 + (3 * (c.stacks 11).length + 3)) + 1, ?_, d.regs, ?_⟩
  · rw [hlength]
    dsimp [budget]
    omega
  · rw [houtput] at hrun
    simpa only [command, program, a] using hrun

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms

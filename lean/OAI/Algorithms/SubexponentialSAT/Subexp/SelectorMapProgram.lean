import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.SelectorIndices
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-!
# A fixed loop applying the selected-index map to query records

The selector uses ports 0--5.  Port 6 is the framed query cursor, port 7
preserves the raw key/payload table, and port 8 accumulates framed answers.
Answers are prepended, so the returned record list reverses query order.
-/

namespace SubexponentialSAT.Subexp.SelectorMapProgram

open BitProgram StructuredCalls

abbrev Data := State 8 9

def ports : RecordPrograms.Ports 8 9 :=
  ⟨5, 6, 7, 6, 2, by decide, by decide, by decide, by decide⟩

def emitPorts : RecordPrograms.Ports 8 9 :=
  ⟨0, 1, 2, 1, 8, by decide, by decide, by decide, by decide⟩

def lowRegs : Fin 5 → Fin 8 := Fin.castAdd 3
def lowStacks : Fin 6 → Fin 9 := Fin.castAdd 3

theorem lowRegs_injective : Function.Injective lowRegs := by
  intro a b h
  exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)

theorem lowStacks_injective : Function.Injective lowStacks := by
  intro a b h
  exact Fin.ext (congrArg (fun x : Fin 9 => x.val) h)

abbrev selector : Program 8 9 (size SelectorProgram.command + 1) :=
  ProgramLinking.liftProgram SelectorProgram.program lowRegs lowStacks

abbrev callback : Cmd 8 9 :=
  .seq (.call (StackRoutines.copyProgram 7 0 4 (0 : Fin 8) 1))
    (.seq (.call selector)
      (.seq (.call (StackRoutines.clearProgram 0 (0 : Fin 8) 1))
        (.seq (.call (StackRoutines.clearProgram 2 (0 : Fin 8) 1))
          (.seq (TupleProgram.pushConst 8 0 false)
            (.seq (TupleProgram.escape emitPorts) (TupleProgram.pushConst 8 0 true))))))

abbrev command : Cmd 8 9 :=
  .seq (TupleProgram.pushConst 8 0 false) (RecordPrograms.iterate ports callback)

abbrev program : Program 8 9 (size command + 1) := compiled command 6 8

def state (regs : Fin 8 → Bool)
    (source output query work3 work4 result cursor table acc : List Bool) : Data :=
  ⟨regs, ![source, output, query, work3, work4, result, cursor, table, acc]⟩

abbrev mergeRegs (base : Fin 8 → Bool) (localRegs : Fin 5 → Bool) : Fin 8 → Bool :=
  ![localRegs 0, localRegs 1, localRegs 2, localRegs 3, localRegs 4, base 5, base 6, base 7]

def selected (records : List (List Bool × List Bool)) (query : List Bool) : List Bool :=
  (records.lookup query).getD query

theorem embed_eq {r s R S : ℕ} (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (base target : State R S) (inner : State r s)
    (hreg : ∀ i, target.regs (reg i) = inner.regs i)
    (hstk : ∀ i, target.stacks (stk i) = inner.stacks i)
    (hfr : ∀ j, (¬ ∃ i, reg i = j) → target.regs j = base.regs j)
    (hfs : ∀ j, (¬ ∃ i, stk i = j) → target.stacks j = base.stacks j) :
    embedState reg stk base inner = target := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [hr.extend_apply]
      exact (hreg i).symm
    · rw [Function.extend_apply' _ _ _ hj]
      exact (hfr j hj).symm
  · funext j
    by_cases hj : ∃ i, stk i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [hs.extend_apply]
      exact (hstk i).symm
    · rw [Function.extend_apply' _ _ _ hj]
      exact (hfs j hj).symm

private theorem instruction_stack_bound {r s l : ℕ} (op : Instr r s l)
    (c : Cfg r s l) (j : Fin s) :
    ((execInstr op c).stacks j).length ≤ (c.stacks j).length + 1 := by
  cases op <;> simp only [execInstr]
  all_goals try omega
  · rename_i stack src next
    by_cases h : j = stack <;> simp [ h]
  · rename_i stack value present next
    by_cases h : j = stack <;> simp [ h] ; omega

private theorem trace_stack_bound {r s l n : ℕ} (p : Program r s l)
    {a b : Cfg r s l} (h : Trace p n a b) (j : Fin s) :
    (b.stacks j).length ≤ (a.stacks j).length + n := by
  induction h with
  | refl => omega
  | @cons n a b c hs ht ih =>
      have hone : (b.stacks j).length ≤ (a.stacks j).length + 1 := by
        cases hp : a.pc with
        | none => simp [step, hp] at hs
        | some label =>
            have hb : execInstr (p.code label) a = b := by simpa [step, hp] using hs
            rw [← hb]
            exact instruction_stack_bound _ _ _
      omega

theorem selector_eval (records : List (List Bool × List Bool)) (query : List Bool)
    (regs : Fin 8 → Bool) (cursor table acc : List Bool) :
    ∃ n ≤ SelectorProgram.budget query records, ∃ localRegs tail,
      tail.length ≤ (SelectorProgram.rawRecords records).length + n ∧
      Eval (.call selector) n
        (state regs (SelectorProgram.rawRecords records) [] query.reverse [] [] [] cursor table acc)
        (state (mergeRegs regs localRegs) tail (selected records query).reverse query.reverse
          [] [] [] cursor table acc) := by
  obtain ⟨n, hn, localRegs, tail, ht⟩ :=
    SelectorProgram.program_trace query records (fun i => regs (lowRegs i))
  have htail := trace_stack_bound SelectorProgram.program ht 0
  let a := state regs (SelectorProgram.rawRecords records) [] query.reverse [] [] [] cursor table acc
  let b := state (mergeRegs regs localRegs) tail (selected records query).reverse query.reverse
    [] [] [] cursor table acc
  have ha : embedState lowRegs lowStacks a
      (SubexpRecordScan.recordState (fun i => regs (lowRegs i))
        (SelectorProgram.rawRecords records) [] query.reverse [] [] []) = a := by
    apply embed_eq _ _ lowRegs_injective lowStacks_injective
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intros; rfl
  have hb : embedState lowRegs lowStacks a
      (SubexpRecordScan.recordState localRegs tail (selected records query).reverse query.reverse [] [] []) = b := by
    apply embed_eq _ _ lowRegs_injective lowStacks_injective
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj
      fin_cases j <;> simp_all [lowRegs, mergeRegs, state, a, b, Fin.exists_fin_succ]
    · intro j hj
      fin_cases j <;> simp_all [lowStacks, state, a, b, Fin.exists_fin_succ]
  refine ⟨n, hn, localRegs, tail, ?_, ?_⟩
  · simpa [SubexpRecordScan.recordState, StructuredProgram.State.withPC] using htail
  · have h := eval_call_lifted SelectorProgram.program lowRegs lowStacks a
      lowRegs_injective lowStacks_injective ht
    change Eval (.call selector) n _
      (embedState lowRegs lowStacks a
        (SubexpRecordScan.recordState localRegs tail (selected records query).reverse
          query.reverse [] [] [])) at h
    rw [ha, hb] at h
    exact h

def callbackCost (records : List (List Bool × List Bool)) (query : List Bool) : ℕ :=
  9 * (SelectorProgram.rawRecords records).length +
    3 * SelectorProgram.budget query records + 2 * query.length +
      5 * (selected records query).length + 18

theorem callback_eval (records : List (List Bool × List Bool)) (query : List Bool)
    (regs : Fin 8 → Bool) (cursor acc : List Bool) :
    ∃ n ≤ callbackCost records query, ∃ regs',
      (∀ j : Fin 3, regs' (Fin.natAdd 5 j) = regs (Fin.natAdd 5 j)) ∧
      Eval callback n
        (state regs [] [] query.reverse [] [] [] cursor (SelectorProgram.rawRecords records) acc)
        (state regs' [] [] [] [] [] [] cursor (SelectorProgram.rawRecords records)
          (TupleProgram.prependRecord (selected records query) acc)) := by
  let a := state regs [] [] query.reverse [] [] [] cursor (SelectorProgram.rawRecords records) acc
  let copied := state (readRegs regs 0 1 none) (SelectorProgram.rawRecords records)
    [] query.reverse [] [] [] cursor (SelectorProgram.rawRecords records) acc
  have hcopy : Eval (.call (StackRoutines.copyProgram 7 0 4 (0 : Fin 8) 1))
      (7 * (SelectorProgram.rawRecords records).length + 5) a copied := by
    have hc : (⟨readRegs a.regs 0 1 none,
        StackRoutines.copyStacks 7 0 a.stacks⟩ : Data) = copied := by
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext j
        fin_cases j <;> simp [a, state, StackRoutines.copyStacks]
    have h := TupleProgram.copy_eval (7 : Fin 9) 0 4 (0 : Fin 8) 1
      (by decide) (by decide) (by decide) (by decide) a (by rfl)
    rw [hc] at h
    exact h
  obtain ⟨ns, hns, localRegs, tail, htail, hselect⟩ :=
    selector_eval records query (readRegs regs 0 1 none) cursor
      (SelectorProgram.rawRecords records) acc
  let c := state (mergeRegs (readRegs regs 0 1 none) localRegs) tail
    (selected records query).reverse query.reverse [] [] [] cursor
      (SelectorProgram.rawRecords records) acc
  let d : Data := ⟨readRegs c.regs 0 1 none, StackRoutines.clearStacks 0 c.stacks⟩
  let e : Data := ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 2 d.stacks⟩
  let f := TupleProgram.pushedState 8 0 false e
  let g := TupleProgram.escapedState emitPorts f
  let h := TupleProgram.pushedState 8 0 true g
  have h1 := TupleProgram.clear_eval (0 : Fin 9) (0 : Fin 8) 1 c
  have h2 := TupleProgram.clear_eval (2 : Fin 9) (0 : Fin 8) 1 d
  have h3 := TupleProgram.pushConst_eval (8 : Fin 9) (0 : Fin 8) false e
  have h4 := TupleProgram.escape_eval_state emitPorts f
  have h5 := TupleProgram.pushConst_eval (8 : Fin 9) (0 : Fin 8) true g
  have hrun := hcopy.seq (hselect.seq (h1.seq (h2.seq (h3.seq (h4.seq h5)))))
  have hh : h = state h.regs [] [] [] [] [] [] cursor (SelectorProgram.rawRecords records)
      (TupleProgram.prependRecord (selected records query) acc) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;>
        simp [ g, f, e, d, c, state, emitPorts, StackRoutines.clearStacks, TupleProgram.prependRecord,
          TupleProgram.frame_eq_escaped, List.append_assoc]
  refine ⟨(7 * (SelectorProgram.rawRecords records).length + 5) +
      (ns + ((2 * tail.length + 3) + ((2 * query.length + 3) +
        (2 + ((5 * (selected records query).length + 3) + 2))))), ?_, h.regs, ?_, ?_⟩
  · dsimp [callbackCost]
    omega
  · intro j
    fin_cases j <;>
      simp [h, g, f, e, d, c, state, emitPorts, mergeRegs, readRegs ]
  · rw [← hh]
    convert hrun using 1 ;
      simp [ c, d, e, f, state, emitPorts,
        StackRoutines.clearStacks ]

def invariant (records : List (List Bool × List Bool)) (a : Data) : Prop :=
  a.stacks 0 = [] ∧ a.stacks 1 = [] ∧ a.stacks 3 = [] ∧
    a.stacks 4 = [] ∧ a.stacks 5 = [] ∧ a.stacks 7 = SelectorProgram.rawRecords records

theorem callback_contract (records : List (List Bool × List Bool)) :
    RecordPrograms.CallbackContractWith ports callback (fun _ => false)
      (callbackCost records) (invariant records)
      (fun query a b => b.stacks 8 =
        TupleProgram.prependRecord (selected records query) (a.stacks 8)) := by
  intro query tail base hb
  let a := RecordPrograms.state ports base false true false tail query.reverse
  have ha : a = state a.regs [] [] query.reverse [] [] [] tail
      (SelectorProgram.rawRecords records) (base.stacks 8) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      rcases hb with ⟨h0, h1, h3, h4, h5, h7⟩
      fin_cases j <;> simp [ ports, h0, h1, h3, h4, h5, h7]
  obtain ⟨n, hn, regs', hr, he⟩ := callback_eval records query a.regs tail (base.stacks 8)
  let b := state regs' [] [] [] [] [] [] tail (SelectorProgram.rawRecords records)
    (TupleProgram.prependRecord (selected records query) (base.stacks 8))
  have hb' : RecordPrograms.state ports b false true false tail [] = b := by
    apply RecordPrograms.state_eq_self
    · simpa [b, state, a, ports, RecordPrograms.state] using hr 0
    · simpa [b, state, a, ports, RecordPrograms.state] using hr 1
    · simpa [b, state, a, ports, RecordPrograms.state] using hr 2
    · rfl
    · rfl
  refine ⟨n, b, hn, ?_, ?_, ?_⟩
  · simp [invariant, b, state]
  · rfl
  · rw [hb']
    simpa only [a, ← ha, b] using he

def recordPrefix (records : List (List Bool)) : List Bool :=
  records.flatMap (fun bits => true :: Encoding.frame bits)

theorem encodeRecords_eq_prefix (records : List (List Bool)) :
    ProgramEncoding.encodeRecords records = recordPrefix records ++ [false] := by
  induction records with
  | nil => rfl
  | cons bits records ih =>
      simp [ProgramEncoding.encodeRecords, Encoding.encodeList, recordPrefix,
        ProgramEncoding.encodeRecords] at ih ⊢
      rw [ih]

theorem fold_prepend (f : List Bool → List Bool) (queries : List (List Bool))
    (acc : List Bool) :
    queries.foldl (fun out query => TupleProgram.prependRecord (f query) out) acc =
      recordPrefix (queries.map f).reverse ++ acc := by
  induction queries generalizing acc with
  | nil => rfl
  | cons query queries ih =>
      rw [List.foldl_cons, ih]
      simp [recordPrefix, TupleProgram.prependRecord,
        List.reverse_cons, List.append_assoc]

def mappedRecords (records : List (List Bool × List Bool)) (queries : List (List Bool)) :=
  (queries.map (selected records)).reverse

def inputStateWith (regs : Fin 8 → Bool) (records : List (List Bool × List Bool))
    (queries : List (List Bool)) : Data :=
  state regs [] [] [] [] [] [] (ProgramEncoding.encodeRecords queries)
    (SelectorProgram.rawRecords records) []

abbrev inputState (records : List (List Bool × List Bool)) (queries : List (List Bool)) : Data :=
  inputStateWith (fun _ => false) records queries

def outputState (records : List (List Bool × List Bool)) (queries : List (List Bool))
    (regs : Fin 8 → Bool) : Data :=
  state regs [] [] [] [] [] [] [] (SelectorProgram.rawRecords records)
    (ProgramEncoding.encodeRecords (mappedRecords records queries))

def budget (records : List (List Bool × List Bool)) (queries : List (List Bool)) : ℕ :=
  6 + RecordPrograms.budget (callbackCost records) queries

/-- The fixed record loop invokes the proved callback for every query. Its
output is the selected payload list in reverse order, and the table survives. -/
theorem program_trace_from (records : List (List Bool × List Bool)) (queries : List (List Bool))
    (initialRegs : Fin 8 → Bool) :
    ∃ n ≤ budget records queries, ∃ regs,
      Trace program n ((inputStateWith initialRegs records queries).withPC (some program.entry))
        ((outputState records queries regs).withPC none) := by
  let a := inputStateWith initialRegs records queries
  let b := TupleProgram.pushedState (8 : Fin 9) (0 : Fin 8) false a
  have hinit := TupleProgram.pushConst_eval (8 : Fin 9) (0 : Fin 8) false a
  have hb : invariant records b := by
    simp [invariant, b, a, inputStateWith, state ]
  obtain ⟨n, next, hn, hnext, history, hiter⟩ :=
    RecordPrograms.iterate_run_with ports callback (fun _ => false) (callbackCost records)
      (invariant records)
      (fun query a b => b.stacks 8 = TupleProgram.prependRecord (selected records query) (a.stacks 8))
      (callback_contract records) queries [] b hb (b.regs 5) (b.regs 6) (b.regs 7)
  have hstart : RecordPrograms.state ports b (b.regs 5) (b.regs 6) (b.regs 7)
      (Encoding.encodeList id queries ++ []) [] = b := by
    apply RecordPrograms.state_eq_self <;>
      simp [ports, b, a, inputStateWith, state,
        ProgramEncoding.encodeRecords]
  have hout : next.stacks 8 = ProgramEncoding.encodeRecords (mappedRecords records queries) := by
    have hh := history.fold_of_false (fun _ _ => rfl) (fun s => s.stacks 8)
      (fun out query => TupleProgram.prependRecord (selected records query) out)
      (fun _ _ _ h => h)
    rw [fold_prepend] at hh
    simpa [b, a, inputStateWith, state, TupleProgram.pushedState,
      mappedRecords, encodeRecords_eq_prefix] using hh
  let c := RecordPrograms.state ports next false true false [] []
  have hiter' : Eval (RecordPrograms.iterate ports callback) n b c := by
    have hany : queries.any (fun _ => false) = false := by
      induction queries <;> simp_all
    simpa only [hstart, hany, TupleProgram.unread_false] using hiter
  have hc : c = outputState records queries c.regs := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      rcases hnext with ⟨h0, h1, h3, h4, h5, h7⟩
      fin_cases j <;>
        simp [ ports, h0, h1, h3, h4, h5, h7, hout]
  have htrace := compiled_halt_trace (hinit.seq hiter') (6 : Fin 9) 8
  refine ⟨2 + n + 1, by dsimp [budget]; omega, c.regs, ?_⟩
  change Trace program (2 + n + 1) (a.withPC (some program.entry)) (c.withPC none) at htrace
  rw [show c.withPC none = (outputState records queries c.regs).withPC none from
    congrArg (fun s : Data => s.withPC none) hc] at htrace
  exact htrace

theorem program_trace (records : List (List Bool × List Bool)) (queries : List (List Bool)) :
    ∃ n ≤ budget records queries, ∃ regs,
      Trace program n ((inputState records queries).withPC (some program.entry))
        ((outputState records queries regs).withPC none) :=
  program_trace_from records queries (fun _ => false)

theorem program_primitive (records : List (List Bool × List Bool)) (queries : List (List Bool)) :
    ∃ regs, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * budget records queries)
      (BitProgram.primitiveCfg program
        ((inputState records queries).withPC (some program.entry)))
      (BitProgram.primitiveCfg program ((outputState records queries regs).withPC none)) := by
  obtain ⟨n, hn, regs, ht⟩ := program_trace records queries
  exact ⟨regs, BitProgram.primitive_execution program ⟨n, hn, ht⟩⟩

theorem selected_length_le (records : List (List Bool × List Bool)) (query : List Bool) :
    (selected records query).length ≤ query.length + (SelectorProgram.rawRecords records).length := by
  induction records with
  | nil => simp [selected, SelectorProgram.rawRecords]
  | cons pair records ih =>
      rcases pair with ⟨key, value⟩
      by_cases h : query = key
      · subst key
        simp [selected, SelectorProgram.rawRecords]
        omega
      · have hs : selected ((key, value) :: records) query = selected records query := by
          simp [selected, List.lookup_cons, beq_false_of_ne h]
        rw [hs]
        simpa [SelectorProgram.rawRecords] using
          ih.trans (by simp [SelectorProgram.rawRecords]; omega)

private theorem oneRecord_bound (key query value : List Bool) :
    SubexpRecordScan.recordCost key query value + 4 ≤
      (9 * query.length + 40) * (2 * key.length + 2 * value.length + 2) := by
  calc
    _ ≤ 40 * (key.length + value.length) + (9 * query.length + 40) := by
      simp only [SubexpRecordScan.recordCost]
      omega
    _ ≤ (9 * query.length + 40) * (key.length + value.length) +
        (9 * query.length + 40) :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _
    _ = (9 * query.length + 40) * (key.length + value.length + 1) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

theorem scanBudget_bound (records : List (List Bool × List Bool)) (query : List Bool) :
    SelectorProgram.scanBudget query records ≤
      (9 * query.length + 40) * (SelectorProgram.rawRecords records).length + 1 := by
  induction records with
  | nil => simp [SelectorProgram.scanBudget, SelectorProgram.rawRecords]
  | cons pair records ih =>
      rcases pair with ⟨key, value⟩
      have h := Nat.add_le_add (oneRecord_bound key query value) ih
      simp only [SelectorProgram.scanBudget, SelectorProgram.rawRecords,
        List.flatMap_cons, List.length_append, Encoding.length_frame] at h ⊢
      nlinarith

theorem selectorBudget_bound (records : List (List Bool × List Bool)) (query : List Bool) :
    SelectorProgram.budget query records ≤
      60 * ((SelectorProgram.rawRecords records).length + 1) * (query.length + 1) := by
  have hs := scanBudget_bound records query
  have hl := selected_length_le records query
  have hm : SelectorProgram.materializeBudget query (records.lookup query) ≤
      7 * (query.length + (SelectorProgram.rawRecords records).length) + 6 := by
    cases he : records.lookup query with
    | none => simp [ SelectorProgram.materializeBudget]
    | some value =>
        simp only [selected, he, Option.getD_some] at hl
        simp [ SelectorProgram.materializeBudget]
        omega
  dsimp [SelectorProgram.budget]
  nlinarith [Nat.zero_le (query.length * (SelectorProgram.rawRecords records).length)]

theorem callbackCost_bound (records : List (List Bool × List Bool)) (query : List Bool) :
    callbackCost records query ≤
      220 * ((SelectorProgram.rawRecords records).length + 1) * (query.length + 1) := by
  have hs := selectorBudget_bound records query
  have hl := selected_length_le records query
  dsimp [callbackCost]
  nlinarith [Nat.zero_le (query.length * (SelectorProgram.rawRecords records).length)]

/-- A polynomial bound in the literal serialized table and query lengths. -/
theorem budget_bound (records : List (List Bool × List Bool)) (queries : List (List Bool)) :
    budget records queries ≤
      500 * ((SelectorProgram.rawRecords records).length + 1) *
        ((ProgramEncoding.encodeRecords queries).length + 1) := by
  let L := (SelectorProgram.rawRecords records).length
  let Q := (ProgramEncoding.encodeRecords queries).length
  have hb := RecordPrograms.program_budget_le_input (callbackCost records) queries
    (220 * (L + 1)) (220 * (L + 1)) (fun query _ => by
      have h := callbackCost_bound records query
      dsimp [L]
      nlinarith)
  change 4 + RecordPrograms.budget (callbackCost records) queries ≤
    (220 * (L + 1) + 220 * (L + 1) + 17) * (Q + 1) at hb
  have hp : 1 ≤ (L + 1) * (Q + 1) := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
  change 6 + RecordPrograms.budget (callbackCost records) queries ≤
    500 * (L + 1) * (Q + 1)
  nlinarith [Nat.zero_le (L * Q)]

theorem program_primitive_polynomial (records : List (List Bool × List Bool))
    (queries : List (List Bool)) :
    ∃ regs, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program *
        (500 * ((SelectorProgram.rawRecords records).length + 1) *
          ((ProgramEncoding.encodeRecords queries).length + 1)))
      (BitProgram.primitiveCfg program
        ((inputState records queries).withPC (some program.entry)))
      (BitProgram.primitiveCfg program ((outputState records queries regs).withPC none)) := by
  obtain ⟨n, hn, regs, ht⟩ := program_trace records queries
  exact ⟨regs, BitProgram.primitive_execution program
    ⟨n, hn.trans (budget_bound records queries), ht⟩⟩

theorem mappedRecords_selection (currentSize : ℕ) (remaining plan : List ℕ) :
    mappedRecords (SelectorProgram.selectionEntries currentSize remaining)
      (plan.reverse.map SelectorProgram.unaryIndex) =
    plan.map (fun n => SelectorProgram.unaryIndex
      (ReadPlan.selectPosition currentSize remaining n)) := by
  simp [mappedRecords, selected, List.map_map, Function.comp_def,
    SelectorProgram.selectionEntries_lookup_default, List.map_reverse]

/-- Reverse the input plan once to obtain selected indices in the original
head/slot order expected by the gather program. -/
theorem selected_plan_trace (currentSize : ℕ) (remaining plan : List ℕ) :
    ∃ n ≤ budget (SelectorProgram.selectionEntries currentSize remaining)
        (plan.reverse.map SelectorProgram.unaryIndex), ∃ regs,
      Trace program n
        ((inputState (SelectorProgram.selectionEntries currentSize remaining)
          (plan.reverse.map SelectorProgram.unaryIndex)).withPC (some program.entry))
        ((state regs [] [] [] [] [] [] []
          (SelectorProgram.rawRecords (SelectorProgram.selectionEntries currentSize remaining))
          (ProgramEncoding.encodeRecords (plan.map (fun n => SelectorProgram.unaryIndex
            (ReadPlan.selectPosition currentSize remaining n))))).withPC none) := by
  obtain ⟨n, hn, regs, ht⟩ := program_trace
    (SelectorProgram.selectionEntries currentSize remaining)
    (plan.reverse.map SelectorProgram.unaryIndex)
  exact ⟨n, hn, regs, by simpa only [outputState, mappedRecords_selection] using ht⟩

end SubexponentialSAT.Subexp.SelectorMapProgram

end OAI.Algorithms

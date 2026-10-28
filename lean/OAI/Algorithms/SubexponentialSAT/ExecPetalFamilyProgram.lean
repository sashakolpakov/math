import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecPetalProgram
import OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.ExecPetalFamilyProgram
open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)

abbrev Regs := Fin 13 → Bool
abbrev Data := State 13 12

def state (regs : Regs) (source payload output clause core : List Bool) : Data :=
  ⟨regs, ![source, payload, output, clause, [], [], [], [], [], [], [], core]⟩

def bankReg (i : Fin 10) : Fin 13 := Fin.castAdd 3 i
def bankStack (i : Fin 9) : Fin 12 := Fin.natAdd 3 i
theorem bankReg_injective : Function.Injective bankReg := Fin.castAdd_injective 10 3
theorem bankStack_injective : Function.Injective bankStack := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [bankStack, Fin.val_natAdd] at this
  omega

abbrev petalCall : Cmd 13 12 :=
  .call (ProgramLinking.liftProgram ExecPetalProgram.program bankReg bankStack)

theorem petalCall_eval (C H : Clause) (regs : Regs) (source payload output : List Bool) :
    ∃ n ≤ 101 * ((encodeClause H).length + 1) * ((encodeClause C).length + 1),
      ∃ rf : Regs, Eval petalCall n
        (state regs source payload output (encodeClause C) (encodeClause H))
        (state rf source payload output (encodeClause (ExecPetalProgram.result C H)) (encodeClause H)) := by
  let d := state regs source payload output (encodeClause C) (encodeClause H)
  obtain ⟨rf, n, hn, ht⟩ := ExecPetalProgram.program_runsIn C H (regs ∘ bankReg)
  let a := ExecPetalProgram.state (regs ∘ bankReg) (encodeClause C) [] [] [] (encodeClause H)
  let b := ExecPetalProgram.state rf (encodeClause (ExecPetalProgram.result C H)) [] [] [] (encodeClause H)
  have hstart : embedState bankReg bankStack d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ bankReg_injective bankStack_injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
  have he := eval_call_lifted ExecPetalProgram.program bankReg bankStack d
    bankReg_injective bankStack_injective ht
  change Eval petalCall n (embedState bankReg bankStack d a) (embedState bankReg bankStack d b) at he
  rw [hstart] at he
  let e := embedState bankReg bankStack d b
  have hs (i : Fin 9) : e.stacks (bankStack i) = b.stacks i :=
    embedState_stack _ _ _ _ bankStack_injective i
  have h0 : e.stacks 0 = source := embedState_stack_frame _ _ _ _ _ (by decide)
  have h1 : e.stacks 1 = payload := embedState_stack_frame _ _ _ _ _ (by decide)
  have h2 : e.stacks 2 = output := embedState_stack_frame _ _ _ _ _ (by decide)
  have heq : e = state e.regs source payload output
      (encodeClause (ExecPetalProgram.result C H)) (encodeClause H) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact hs 0
    · exact hs 1
    · exact hs 2
    · exact hs 3
    · exact hs 4
    · exact hs 5
    · exact hs 6
    · exact hs 7
    · exact hs 8
  exact ⟨n, hn, e.regs, heq ▸ he⟩

abbrev transfer (src dst : Fin 12) : Cmd 13 12 :=
  .call (StackRoutines.transferProgram src dst 0 1)

theorem transfer_in (regs : Regs) (source output bits core : List Bool) :
    Eval (transfer 1 3) (3 * bits.length + 3)
      (state regs source bits.reverse output [] core)
      (state (readRegs regs 0 1 none) source [] output bits core) := by
  have h := ListRegisterProgram.transfer_run (r := 13) (s := 12) 1 3 0 1
    (by decide) (by decide) regs (state regs source bits.reverse output [] core).stacks
  have hs : StackRoutines.transferStacks 1 3 (state regs source bits.reverse output [] core).stacks =
      (state (readRegs regs 0 1 none) source [] output bits core).stacks := by
    funext i
    fin_cases i <;> simp [state, StackRoutines.transferStacks]
  have hlen : ((state regs source bits.reverse output [] core).stacks 1).length = bits.length := by
    simp [state]
  rw [hs] at h
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, state, hlen] using h

theorem transfer_out (regs : Regs) (source output bits core : List Bool) :
    Eval (transfer 3 1) (3 * bits.length + 3)
      (state regs source [] output bits core)
      (state (readRegs regs 0 1 none) source bits.reverse output [] core) := by
  have h := ListRegisterProgram.transfer_run (r := 13) (s := 12) 3 1 0 1
    (by decide) (by decide) regs (state regs source [] output bits core).stacks
  have hs : StackRoutines.transferStacks 3 1 (state regs source [] output bits core).stacks =
      (state (readRegs regs 0 1 none) source bits.reverse output [] core).stacks := by
    funext i
    fin_cases i <;> simp [state, StackRoutines.transferStacks]
  have hlen : ((state regs source [] output bits core).stacks 3).length = bits.length := by
    simp [state]
  rw [hs] at h
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, state, hlen] using h

def emitReg : Fin 3 → Fin 13 := ![10, 11, 12]
def emitStack : Fin 4 → Fin 12 := ![0, 3, 2, 1]
theorem emitReg_injective : Function.Injective emitReg := by decide
theorem emitStack_injective : Function.Injective emitStack := by decide
abbrev emit : Cmd 13 12 := .call
  (ProgramLinking.liftProgram SubexpNormalizeProgram.emitIfSelectedProgram emitReg emitStack)

def flags (regs : Regs) (v p f : Bool) : Regs :=
  Function.update (Function.update (Function.update regs 10 v) 11 p) 12 f

@[simp] theorem flags_self (regs : Regs) : flags regs (regs 10) (regs 11) (regs 12) = regs := by
  funext i
  by_cases h10 : i = 10 <;> by_cases h11 : i = 11 <;> by_cases h12 : i = 12 <;>
    simp_all [flags]

private theorem embed_emit (regs : Regs) (v p f : Bool)
    (source₀ payload₀ output₀ source payload output work core : List Bool) :
    embedState emitReg emitStack (state regs source₀ payload₀ output₀ [] core)
      (SubexpNormalizeProgram.filterState v p f source work output payload) =
      state (flags regs v p f) source payload output work core := by
  apply embedState_eq_of_ports _ _ _ _ _ emitReg_injective emitStack_injective
  · intro i; fin_cases i <;> simp [emitReg, flags, state, SubexpNormalizeProgram.filterState]
  · intro i hi
    have h10 : i ≠ 10 := fun h => hi ⟨0, h.symm⟩
    have h11 : i ≠ 11 := fun h => hi ⟨1, h.symm⟩
    have h12 : i ≠ 12 := fun h => hi ⟨2, h.symm⟩
    simp [state, flags, h10, h11, h12]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨1, h.symm⟩
    have h2 : i ≠ 2 := fun h => hi ⟨2, h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨3, h.symm⟩
    fin_cases i <;> simp_all [state]

theorem emit_eval (regs : Regs) (bits source output core : List Bool) (hsel : regs 12 = true) :
    Eval emit (5 * bits.length + 12)
      (state regs source bits.reverse output [] core)
      (state (flags regs false true false) source []
        (true :: (Encoding.frame bits ++ output)) [] core) := by
  have h := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram emitReg emitStack
    (state regs source bits.reverse output [] core) emitReg_injective emitStack_injective
    (SubexpNormalizeProgram.emitIfSelected_trace true bits source [] output (regs 10) (regs 11))
  rw [embed_emit, embed_emit] at h
  have hflags : flags regs (regs 10) (regs 11) true = regs := by
    simpa only [hsel] using flags_self regs
  simpa [hflags, SubexpNormalizeProgram.emitIfSelectedSteps] using h

abbrev callback : Cmd 13 12 := .seq (transfer 1 3) (.seq petalCall
  (.seq (transfer 3 1) (.seq (RecordPrograms.atom (.set 12 true)) emit)))

def cost (H : Clause) (bits : List Bool) : ℕ :=
  140 * ((encodeClause H).length + 1) * (bits.length + 1)

theorem callback_eval (C H : Clause) (regs : Regs) (source output : List Bool) :
    ∃ n ≤ cost H (encodeClause C), ∃ rf : Regs,
      rf 10 = false ∧ rf 11 = true ∧ rf 12 = false ∧
      Eval callback n (state regs source (encodeClause C).reverse output [] (encodeClause H))
        (state rf source []
          (true :: (Encoding.frame (encodeClause (ExecPetalProgram.result C H)) ++ output))
          [] (encodeClause H)) := by
  obtain ⟨n, hn, rf, he⟩ := petalCall_eval C H (readRegs regs 0 1 none) source [] output
  let restored := readRegs rf 0 1 none
  let selected := Function.update restored 12 true
  have hset : Eval (RecordPrograms.atom (.set 12 true)) 1
      (state restored source (encodeClause (ExecPetalProgram.result C H)).reverse output [] (encodeClause H))
      (state selected source (encodeClause (ExecPetalProgram.result C H)).reverse output [] (encodeClause H)) :=
    .base (.atom _ _)
  have hfull := (transfer_in regs source output (encodeClause C) (encodeClause H)).seq
    (he.seq ((transfer_out rf source output (encodeClause (ExecPetalProgram.result C H))
      (encodeClause H)).seq (hset.seq (emit_eval selected _ _ _ _ (by simp [selected])))))
  have hlen := ExecPetalProgram.result_encoded_length_le id C H
  change (encodeClause (ExecPetalProgram.result C H)).length ≤ (encodeClause C).length at hlen
  refine ⟨_, ?_, flags selected false true false, ?_, ?_, ?_, hfull⟩
  · dsimp [cost]
    nlinarith
  · simp [flags]
  · simp [flags]
  · simp [flags]

def ports : RecordPrograms.Ports 13 12 where
  tag := 10
  present := 11
  found := 12
  source := 0
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

theorem record_state (regs : Regs) (source payload output clause core tail bits : List Bool)
    (v p f : Bool) :
    RecordPrograms.state ports (state regs source payload output clause core) v p f tail bits =
      state (flags regs v p f) tail bits output clause core := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [ ports, state]

def invariant (H : Clause) (d : Data) : Prop :=
  ∃ regs source output payload, d = state regs source payload output [] (encodeClause H)

def mapPayload (H : Clause) (bits : List Bool) : List Bool :=
  encodeClause (ExecPetalProgram.result ((ExecClauseFiltersProgram.decodeClause bits).getD []) H)

@[simp] theorem mapPayload_encodeClause (C H : Clause) :
    mapPayload H (encodeClause C) = encodeClause (ExecPetalProgram.result C H) := by
  simp [mapPayload]

def Effect (H : Clause) (bits : List Bool) (before after : Data) : Prop :=
  after.stacks 2 = true :: (Encoding.frame (mapPayload H bits) ++ before.stacks 2)

theorem callback_contract (H : Clause) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false) (cost H)
      (invariant H) (Effect H) ExecClauseFiltersProgram.ClausePayload := by
  intro bits tail base hbits hbase
  obtain ⟨C, rfl⟩ := hbits
  obtain ⟨regs, source, output, payload, rfl⟩ := hbase
  obtain ⟨n, hn, rf, h10, h11, h12, he⟩ :=
    callback_eval C H (flags regs false true false) tail output
  let out := true :: (Encoding.frame (encodeClause (ExecPetalProgram.result C H)) ++ output)
  let next := state rf [] [] out [] (encodeClause H)
  have hflags : flags rf false true false = rf := by
    simpa only [h10, h11, h12] using flags_self rf
  refine ⟨n, next, hn, ⟨rf, [], out, [], rfl⟩, ?_, ?_⟩
  · simp [Effect, next, state, out]
  · simpa only [next, record_state, hflags] using he

theorem visits_result (H : Clause) {records : List (List Bool)} {before after : Data}
    (h : RecordPrograms.Visits (fun _ => false) (Effect H) records before after)
    (acc : List (List Bool)) (hacc : before.stacks 2 = Encoding.encodeList id acc) :
    after.stacks 2 = Encoding.encodeList id ((records.map (mapPayload H)).reverse ++ acc) := by
  induction h generalizing acc with
  | nil base => simpa using hacc
  | hit ht _ => cases ht
  | @miss bits records before middle after _ he _ ih =>
    have hm : middle.stacks 2 = Encoding.encodeList id (mapPayload H bits :: acc) := by
      simpa [Effect, hacc, Encoding.encodeList] using he
    simpa [List.map_cons, List.reverse_cons, List.append_assoc] using ih _ hm

def petals (F : Formula) (H : Clause) : Formula := F.map (fun C => ExecPetalProgram.result C H)

theorem records_map (F : Formula) (H : Clause) :
    (ExecClauseFiltersProgram.formulaRecords F).map (mapPayload H) =
      ExecClauseFiltersProgram.formulaRecords (petals F H) := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    simp [ExecClauseFiltersProgram.formulaRecords, petals] at ih ⊢

abbrev scan : Cmd 13 12 := RecordPrograms.iterate ports callback

theorem budget_le (H : Clause) (records : List (List Bool)) :
    3 + RecordPrograms.budget (cost H) records ≤
      160 * ((encodeClause H).length + 1) * ((Encoding.encodeList id records).length + 1) := by
  induction records with
  | nil => simp [RecordPrograms.budget, Encoding.encodeList]; omega
  | cons x xs ih =>
    simp only [RecordPrograms.budget, cost, Encoding.length_encodeList_cons, id_eq]
    nlinarith

theorem scan_eval (F : Formula) (H : Clause) (acc : List (List Bool)) (regs : Regs) :
    ∃ n ≤ 160 * ((encodeClause H).length + 1) * ((encodeFormula F).length + 1),
      ∃ rf : Regs, Eval scan n
        (state regs (encodeFormula F) [] (Encoding.encodeList id acc) [] (encodeClause H))
        (state rf [] [] (Encoding.encodeList id
          ((ExecClauseFiltersProgram.formulaRecords (petals F H)).reverse ++ acc)) [] (encodeClause H)) := by
  let d := state regs (encodeFormula F) [] (Encoding.encodeList id acc) [] (encodeClause H)
  obtain ⟨n, next, hn, hnext, hhistory, he⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (cost H) (invariant H) (Effect H)
    ExecClauseFiltersProgram.ClausePayload (callback_contract H)
    (ExecClauseFiltersProgram.formulaRecords F) [] d
    (ExecClauseFiltersProgram.valid_formulaRecords F) ⟨regs, _, _, [], rfl⟩
    (regs 10) (regs 11) (regs 12)
  have hout := visits_result H hhistory acc (show d.stacks 2 = _ from rfl)
  obtain ⟨rf, source, output, payload, rfl⟩ := hnext
  have hout' : output = Encoding.encodeList id
      ((ExecClauseFiltersProgram.formulaRecords (petals F H)).reverse ++ acc) := by
    simpa [state, records_map] using hout
  have hany : (ExecClauseFiltersProgram.formulaRecords F).any (fun _ => false) = false := by simp
  refine ⟨n, hn.trans ?_, flags rf false true false, ?_⟩
  · simpa only [← ExecClauseFiltersProgram.encodeFormula_records] using
      budget_le H (ExecClauseFiltersProgram.formulaRecords F)
  · simpa only [d, List.append_nil, record_state, flags_self,
      ← ExecClauseFiltersProgram.encodeFormula_records, hany,
      SubexpNormalizeProgram.unread_false, hout'] using he

abbrev pushOutput : Cmd 13 12 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push 2 0))

theorem pushOutput_eval (regs : Regs) (source output core : List Bool) :
    Eval pushOutput 2 (state regs source [] output [] core)
      (state (Function.update regs 0 false) source [] (false :: output) [] core) := by
  have h := Eval.seq
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (r := 13) (s := 12) 0 false)
      (state regs source [] output [] core)))
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 13) (s := 12) 2 0)
      ((StructuredProgram.Atom.set 0 false).eval (state regs source [] output [] core))))
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [state, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
 StructuredProgram.State.ofCfg, execInstr]

abbrev command : Cmd 13 12 := .seq pushOutput scan
def program := compiled command 0 2

theorem command_eval (F : Formula) (H : Clause) (regs : Regs) :
    ∃ n ≤ 160 * ((encodeClause H).length + 1) * ((encodeFormula F).length + 1) + 2,
      ∃ rf : Regs, Eval command n
        (state regs (encodeFormula F) [] [] [] (encodeClause H))
        (state rf [] [] (Encoding.encodeList id
          (ExecClauseFiltersProgram.formulaRecords (petals F H)).reverse) [] (encodeClause H)) := by
  obtain ⟨n, hn, rf, he⟩ := scan_eval F H [] (Function.update regs 0 false)
  simp only [List.append_nil] at he
  exact ⟨2 + n, by omega, rf, (pushOutput_eval regs _ [] _).seq he⟩

theorem program_runsIn (F : Formula) (H : Clause) (regs : Regs) :
    ∃ rf : Regs, RunsIn program
      (170 * ((encodeClause H).length + 1) * ((encodeFormula F).length + 1))
      ((state regs (encodeFormula F) [] [] [] (encodeClause H)).withPC (some program.entry))
      ((state rf [] [] (Encoding.encodeList id
        (ExecClauseFiltersProgram.formulaRecords (petals F H)).reverse) [] (encodeClause H)).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := command_eval F H regs
  exact ⟨rf, n + 1, by nlinarith, compiled_halt_trace he 0 2⟩

end SubexponentialSAT.ExecPetalFamilyProgram

end OAI.Algorithms

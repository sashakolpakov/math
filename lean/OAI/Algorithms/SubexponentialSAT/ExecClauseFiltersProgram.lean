import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScanPreserve
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ExecCNFSemanticHelpers

namespace OAI.Algorithms

/-!
# Exact-order clause filters on encoded formulas

The relation scanner occupies stacks 0--12. The outer record pass uses stack
13 for unread records, stack 14 for the reversed output record list, and stack
15 for the reversed current payload. Two stack transfers put a clause into the
scanner and return it to the existing frame emitter.
-/


namespace SubexponentialSAT.ExecClauseFiltersProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula Mode encodeClause encodeFormula test)

abbrev Regs := Fin 15 → Bool
abbrev Data := StructuredProgram.State 15 16

def smallState (regs : Regs) (query answer master : List Bool) :
    StructuredProgram.State 15 13 :=
  ⟨regs, ![[], [], [], [], [], [], [], [], [], query, [], answer, master]⟩

def state (regs : Regs) (query answer master source output payload : List Bool) : Data :=
  ⟨regs, ![[], [], [], [], [], [], [], [], [], query, [], answer, master,
    source, output, payload]⟩

def scanStack (i : Fin 13) : Fin 16 := Fin.castAdd 3 i

theorem scanStack_injective : Function.Injective scanStack := Fin.castAdd_injective 13 3

private theorem embed_smallState (frameRegs regs : Regs)
    (query0 answer0 master0 query answer master source output payload : List Bool) :
    embedState id scanStack (state frameRegs query0 answer0 master0 source output payload)
      (smallState regs query answer master) = state regs query answer master source output payload := by
  apply embedState_eq_of_ports id scanStack _ _ _ Function.injective_id scanStack_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have hlo : 13 ≤ i.val := by
      by_contra h
      have hil : i.val < 13 := by omega
      exact hi ⟨⟨i.val, hil⟩, Fin.ext rfl⟩
    fin_cases i <;> simp_all [state]

abbrev scan (mode : Mode) : Cmd 15 16 :=
  .call (ProgramLinking.liftProgram (ExecClauseRelationScan.Preserving.program mode) id scanStack)

theorem scan_eval (mode : Mode) (F : Formula) (Q : Clause) (regs : Regs)
    (source output : List Bool) :
    ∃ (n : ℕ) (rf : Regs), n ≤ ExecClauseRelationScan.Preserving.bound F Q ∧
      rf 14 = F.any (fun C => test mode C Q) ∧
      Eval (scan mode) n
        (state regs (encodeClause Q) [] (encodeFormula F) source output [])
        (state rf (encodeClause Q) [F.any (fun C => test mode C Q)]
          (encodeFormula F) source output []) := by
  let start := smallState regs (encodeClause Q) [] (encodeFormula F)
  have hv : ExecClauseRelationScan.Preserving.invariant F Q start := by
    refine ⟨rfl, ⟨rfl, ?_⟩, rfl⟩
    intro i
    fin_cases i <;> rfl
  obtain ⟨e, ⟨n, hn, htrace⟩, he, hr, ho⟩ :=
    ExecClauseRelationScan.Preserving.program_runsIn mode F Q start hv rfl
  have heq : e = smallState e.regs (encodeClause Q)
      [F.any (fun C => test mode C Q)] (encodeFormula F) := by
    have hs : e.stacks = (smallState e.regs (encodeClause Q)
        [F.any (fun C => test mode C Q)] (encodeFormula F)).stacks := by
      funext i
      fin_cases i
      · exact he.2.1.2 0
      · exact he.2.1.2 1
      · exact he.2.1.2 2
      · exact he.2.1.2 3
      · exact he.2.1.2 4
      · exact he.2.1.2 5
      · exact he.2.1.2 6
      · exact he.2.1.2 7
      · exact he.2.1.2 8
      · exact he.2.1.1
      · exact he.2.2
      · exact ho
      · exact he.1
    cases e
    cases hs
    rfl
  have hcall := eval_call_lifted (ExecClauseRelationScan.Preserving.program mode)
    id scanStack (state regs (encodeClause Q) [] (encodeFormula F) source output [])
    Function.injective_id scanStack_injective htrace
  rw [heq] at hcall
  change Eval (scan mode) n
    (embedState id scanStack _ (smallState regs (encodeClause Q) [] (encodeFormula F))) _ at hcall
  rw [embed_smallState, embed_smallState] at hcall
  exact ⟨n, e.regs, hn, hr, hcall⟩

abbrev transfer (source target : Fin 16) : Cmd 15 16 :=
  .call (StackRoutines.transferProgram source target 0 1)

def transferred (source target : Fin 16) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks source target d.stacks⟩

theorem transfer_eval (source target : Fin 16) (d : Data) (hne : source ≠ target) :
    Eval (transfer source target) (3 * (d.stacks source).length + 3)
      d (transferred source target d) :=
  .call _ (ListRegisterProgram.transfer_run source target 0 1 hne (by decide) d.regs d.stacks)

abbrev clear (port : Fin 16) : Cmd 15 16 := .call (StackRoutines.clearProgram port 0 1)

def cleared (port : Fin 16) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks port d.stacks⟩

theorem clear_eval (port : Fin 16) (d : Data) :
    Eval (clear port) (2 * (d.stacks port).length + 3) d (cleared port d) :=
  .call _ (ListRegisterProgram.clear_run port 0 1 d.regs d.stacks)

def reset (regs : Regs) : Regs := readRegs regs 0 1 none

theorem transfer_into_query (regs : Regs) (bits master source output : List Bool) :
    Eval (transfer 15 9) (3 * bits.length + 3)
      (state regs [] [] master source output bits.reverse)
      (state (reset regs) bits [] master source output []) := by
  have heq : transferred 15 9 (state regs [] [] master source output bits.reverse) =
      state (reset regs) bits [] master source output [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [ state, StackRoutines.transferStacks]
  have h := transfer_eval 15 9 (state regs [] [] master source output bits.reverse) (by decide)
  rw [heq] at h
  simpa [state] using h

theorem transfer_from_query (regs : Regs) (bits master source output : List Bool) :
    Eval (transfer 9 15) (3 * bits.length + 3)
      (state regs bits [] master source output [])
      (state (reset regs) [] [] master source output bits.reverse) := by
  have heq : transferred 9 15 (state regs bits [] master source output []) =
      state (reset regs) [] [] master source output bits.reverse := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [ state, StackRoutines.transferStacks]
  have h := transfer_eval 9 15 (state regs bits [] master source output []) (by decide)
  rw [heq] at h
  simpa [state] using h

theorem clear_answer (regs : Regs) (answer : Bool) (query master source output : List Bool) :
    Eval (clear 11) 5
      (state regs query [answer] master source output [])
      (state (reset regs) query [] master source output []) := by
  have heq : cleared 11 (state regs query [answer] master source output []) =
      state (reset regs) query [] master source output [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [ state, StackRoutines.clearStacks]
  have h := clear_eval 11 (state regs query [answer] master source output [])
  rw [heq] at h
  simpa [state] using h

def flags (regs : Regs) (value present selected : Bool) : Regs :=
  Function.update (Function.update (Function.update regs 0 value) 1 present) 14 selected

@[simp] theorem flags_self (regs : Regs) : flags regs (regs 0) (regs 1) (regs 14) = regs := by
  funext i
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> by_cases h14 : i = 14 <;>
    simp_all [flags]

def emitRegs : Fin 3 → Fin 15 := ![0, 1, 14]
def emitStacks : Fin 4 → Fin 16 := ![13, 9, 14, 15]

theorem emitRegs_injective : Function.Injective emitRegs := by decide
theorem emitStacks_injective : Function.Injective emitStacks := by decide

abbrev emit : Cmd 15 16 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.emitIfSelectedProgram emitRegs emitStacks)

private theorem embed_emit (regs : Regs) (value present selected : Bool)
    (query0 source0 output0 payload0 query source output payload answer master : List Bool) :
    embedState emitRegs emitStacks (state regs query0 answer master source0 output0 payload0)
      (SubexpNormalizeProgram.filterState value present selected source query output payload) =
      state (flags regs value present selected) query answer master source output payload := by
  apply embedState_eq_of_ports emitRegs emitStacks _ _ _ emitRegs_injective emitStacks_injective
  · intro i
    fin_cases i <;> simp [emitRegs, flags, state, SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.triple]
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
    have h14 : i ≠ 14 := fun h => hi ⟨2, h.symm⟩
    simp [state, flags, h0, h1, h14]
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have h13 : i ≠ 13 := fun h => hi ⟨0, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨1, h.symm⟩
    have h14 : i ≠ 14 := fun h => hi ⟨2, h.symm⟩
    have h15 : i ≠ 15 := fun h => hi ⟨3, h.symm⟩
    fin_cases i <;> simp_all [state]

theorem emit_eval (regs : Regs) (bits master source output : List Bool) :
    Eval emit (SubexpNormalizeProgram.emitIfSelectedSteps (regs 14) bits + 1)
      (state regs [] [] master source output bits.reverse)
      (state (flags regs false true false) [] [] master source
        (if regs 14 then true :: (Encoding.frame bits ++ output) else output) []) := by
  have h := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram emitRegs emitStacks
    (state regs [] [] master source output bits.reverse) emitRegs_injective emitStacks_injective
    (SubexpNormalizeProgram.emitIfSelected_trace (regs 14) bits source [] output (regs 0) (regs 1))
  simpa only [embed_emit, flags_self, emit] using h

abbrev callback (mode : Mode) : Cmd 15 16 :=
  .seq (transfer 15 9) (.seq (scan mode) (.seq (clear 11)
    (.seq (transfer 9 15) (.seq (.base (.atom (.bnot 14 14))) emit))))

def callbackBound (F : Formula) (Q : Clause) : ℕ :=
  ExecClauseRelationScan.Preserving.bound F Q + 11 * (encodeClause Q).length + 25

/-- A complete encoded clause-selection callback, including the actual
relation scan, result cleanup, and framed output emission. -/
theorem callback_eval (mode : Mode) (F : Formula) (Q : Clause) (regs : Regs)
    (source output : List Bool) :
    ∃ (n : ℕ) (rf : Regs), n ≤ callbackBound F Q ∧
      rf 0 = false ∧ rf 1 = true ∧ rf 14 = false ∧
      Eval (callback mode) n
        (state regs [] [] (encodeFormula F) source output (encodeClause Q).reverse)
        (state rf [] [] (encodeFormula F) source
          (if !(F.any (fun C => test mode C Q)) then
            true :: (Encoding.frame (encodeClause Q) ++ output) else output) []) := by
  obtain ⟨n, scanned, hn, hflag, hscan⟩ :=
    scan_eval mode F Q (reset regs) source output
  let restored := reset (reset scanned)
  let flipped := Function.update restored 14 (!(restored 14))
  have hflip : Eval (.base (.atom (.bnot 14 14))) 1
      (state restored [] [] (encodeFormula F) source output (encodeClause Q).reverse)
      (state flipped [] [] (encodeFormula F) source output (encodeClause Q).reverse) := by
    exact .base (.atom _ _)
  have hselected : flipped 14 = !(F.any (fun C => test mode C Q)) := by
    simp [flipped, restored, reset, readRegs, hflag]
  have hemit := emit_eval flipped (encodeClause Q) (encodeFormula F) source output
  rw [hselected] at hemit
  have hfull := (transfer_into_query regs (encodeClause Q) (encodeFormula F) source output).seq
    (hscan.seq ((clear_answer scanned (F.any (fun C => test mode C Q))
      (encodeClause Q) (encodeFormula F) source output).seq
      ((transfer_from_query (reset scanned) (encodeClause Q) (encodeFormula F) source output).seq
        (hflip.seq hemit))))
  refine ⟨_, flags flipped false true false, ?_, ?_, ?_, ?_, hfull⟩
  · have hcost := SubexpNormalizeProgram.emitIfSelected_steps_le
      (!(F.any (fun C => test mode C Q))) (encodeClause Q)
    unfold callbackBound
    omega
  · simp [flags]
  · simp [flags]
  · simp [flags]

def ports : RecordPrograms.Ports 15 16 where
  tag := 0
  present := 1
  found := 14
  source := 13
  payload := 15
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

theorem record_state (regs : Regs) (query answer master source output payload tail bits : List Bool)
    (v p f : Bool) :
    RecordPrograms.state ports (state regs query answer master source output payload)
      v p f tail bits = state (flags regs v p f) query answer master tail output bits := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [ ports, state]

def invariant (F : Formula) (d : Data) : Prop :=
  ∃ regs source output payload, d = state regs [] [] (encodeFormula F) source output payload

theorem state_invariant (F : Formula) (regs : Regs) (source output payload : List Bool) :
    invariant F (state regs [] [] (encodeFormula F) source output payload) :=
  ⟨regs, source, output, payload, rfl⟩

def decodeClause (bits : List Bool) : Option Clause := do
  let (fields, rest) ← ProgramEncoding.readRecords bits
  if rest.isEmpty then some fields else none

@[simp] theorem decodeClause_encodeClause (Q : Clause) :
    decodeClause (encodeClause Q) = some Q := by
  change (do
    let (fields, rest) ← ProgramEncoding.readRecords (ProgramEncoding.encodeRecords Q)
    if rest.isEmpty then some fields else none) = some Q
  simp

def keep (mode : Mode) (F : Formula) (bits : List Bool) : Bool :=
  match decodeClause bits with
  | some Q => !(F.any (fun C => test mode C Q))
  | none => false

@[simp] theorem keep_encodeClause (mode : Mode) (F : Formula) (Q : Clause) :
    keep mode F (encodeClause Q) = !(F.any (fun C => test mode C Q)) := by
  simp [keep]

def ClausePayload (bits : List Bool) : Prop := ∃ Q : Clause, bits = encodeClause Q

def perClauseCost (F : Formula) (bits : List Bool) : ℕ :=
  600 * ((encodeFormula F).length + 1) * (bits.length + 1)

theorem callbackBound_le (F : Formula) (Q : Clause) :
    callbackBound F Q ≤ perClauseCost F (encodeClause Q) := by
  unfold callbackBound perClauseCost ExecClauseRelationScan.Preserving.bound
  nlinarith

theorem callback_contract (mode : Mode) (F : Formula) :
    RecordPrograms.CallbackContractWithOn ports (callback mode) (fun _ => false)
      (perClauseCost F) (invariant F) (SubexpNormalizeProgram.FilterEffect 14 (keep mode F))
      ClausePayload := by
  intro bits tail base hbits hbase
  obtain ⟨Q, rfl⟩ := hbits
  obtain ⟨regs, source, output, payload, rfl⟩ := hbase
  obtain ⟨n, rf, hn, h0, h1, h14, he⟩ :=
    callback_eval mode F Q (flags regs false true false) tail output
  let newOutput := if !(F.any (fun C => test mode C Q)) then
    true :: (Encoding.frame (encodeClause Q) ++ output) else output
  let next := state rf [] [] (encodeFormula F) [] newOutput []
  have hflags : flags rf false true false = rf := by
    simpa only [h0, h1, h14] using flags_self rf
  refine ⟨n, next, hn.trans (callbackBound_le F Q), state_invariant _ _ _ _ _, ?_, ?_⟩
  · simp [SubexpNormalizeProgram.FilterEffect, next, newOutput, state]
  · simpa only [next, record_state, hflags] using he

def formulaRecords (F : Formula) : List (List Bool) := F.map encodeClause

theorem encodeFormula_records (F : Formula) :
    encodeFormula F = Encoding.encodeList id (formulaRecords F) := by
  induction F with
  | nil => rfl
  | cons C F ih => simpa [encodeFormula, formulaRecords, Encoding.encodeList] using ih

theorem valid_formulaRecords (F : Formula) :
    ∀ bits ∈ formulaRecords F, ClausePayload bits := by
  intro bits hb
  obtain ⟨C, _, rfl⟩ := List.mem_map.mp hb
  exact ⟨C, rfl⟩

def filtered (mode : Mode) (master F : Formula) : Formula :=
  F.filter (fun Q => !(master.any (fun C => test mode C Q)))

theorem filtered_formulaRecords (mode : Mode) (master F : Formula) :
    (formulaRecords F).filter (keep mode master) = formulaRecords (filtered mode master F) := by
  induction F with
  | nil => rfl
  | cons Q F ih =>
    simp only [formulaRecords, filtered] at ih
    cases h : !(master.any (fun C => test mode C Q)) <;>
      simp [formulaRecords, filtered, h, ih]

theorem filtered_length_le (mode : Mode) (master F : Formula) :
    (encodeFormula (filtered mode master F)).length ≤ (encodeFormula F).length :=
  Encoding.length_encodeList_filter_le encodeClause
    (fun Q => !(master.any (fun C => test mode C Q))) F

theorem filter_budget_le (master : Formula) (records : List (List Bool)) :
    3 + RecordPrograms.budget (perClauseCost master) records ≤
      620 * ((encodeFormula master).length + 1) *
        ((Encoding.encodeList id records).length + 1) := by
  induction records with
  | nil => simp [RecordPrograms.budget, Encoding.encodeList]; omega
  | cons bits records ih =>
    simp only [RecordPrograms.budget, perClauseCost, Encoding.length_encodeList_cons, id_eq]
    nlinarith

theorem encoded_reverse_length (records : List (List Bool)) :
    (Encoding.encodeList id records.reverse).length = (Encoding.encodeList id records).length := by
  change (ProgramEncoding.encodeRecords records.reverse).length =
    (ProgramEncoding.encodeRecords records).length
  simp [ProgramEncoding.encodeRecords_length, List.map_reverse]

abbrev filterScan (mode : Mode) : Cmd 15 16 := RecordPrograms.iterate ports (callback mode)

theorem filterScan_eval (mode : Mode) (master F : Formula) (acc : List (List Bool)) (regs : Regs) :
    ∃ n ≤ 620 * ((encodeFormula master).length + 1) * ((encodeFormula F).length + 1),
      ∃ rf : Regs, Eval (filterScan mode) n
        (state regs [] [] (encodeFormula master) (encodeFormula F) (Encoding.encodeList id acc) [])
        (state rf [] [] (encodeFormula master) []
          (Encoding.encodeList id ((formulaRecords (filtered mode master F)).reverse ++ acc)) []) := by
  let d := state regs [] [] (encodeFormula master) (encodeFormula F) (Encoding.encodeList id acc) []
  obtain ⟨n, next, hn, hnext, hhistory, he⟩ := RecordPrograms.iterate_run_with_on
    ports (callback mode) (fun _ => false) (perClauseCost master) (invariant master)
    (SubexpNormalizeProgram.FilterEffect 14 (keep mode master)) ClausePayload
    (callback_contract mode master) (formulaRecords F) [] d (valid_formulaRecords F)
    (state_invariant _ _ _ _ _) (regs 0) (regs 1) (regs 14)
  have hout := SubexpNormalizeProgram.filterVisits_result 14 (keep mode master) hhistory acc
    (show d.stacks 14 = Encoding.encodeList id acc from rfl)
  obtain ⟨rf, source, output, payload, rfl⟩ := hnext
  have hany : (formulaRecords F).any (fun _ => false) = false := by simp
  have hout' : output = Encoding.encodeList id
      ((formulaRecords (filtered mode master F)).reverse ++ acc) := by
    change output = Encoding.encodeList id
      (((formulaRecords F).filter (keep mode master)).reverse ++ acc) at hout
    simpa only [filtered_formulaRecords] using hout
  refine ⟨n, ?_, flags rf false true false, ?_⟩
  · exact hn.trans (by simpa only [← encodeFormula_records] using filter_budget_le master (formulaRecords F))
  · simpa only [d, List.append_nil, record_state, flags_self, ← encodeFormula_records,
      hany, SubexpNormalizeProgram.unread_false, hout'] using he

abbrev copyMaster : Cmd 15 16 := .call (StackRoutines.copyProgram 13 12 9 0 1)

theorem copyMaster_eval (regs : Regs) (source output payload : List Bool) :
    Eval copyMaster (7 * source.length + 5)
      (state regs [] [] [] source output payload)
      (state (reset regs) [] [] source source output payload) := by
  have h := ListRegisterProgram.copy_run (13 : Fin 16) 12 9 (0 : Fin 15) 1
    (by decide) (by decide) (by decide) (by decide)
    regs (state regs [] [] [] source output payload).stacks rfl
  have hs : StackRoutines.copyStacks 13 12
      (state regs [] [] [] source output payload).stacks =
      (state (reset regs) [] [] source source output payload).stacks := by
    funext i
    fin_cases i <;> simp [StackRoutines.copyStacks, state]
  rw [hs] at h
  apply Eval.call
  simpa [copyMaster, ListRegisterProgram.Run, reset, state] using h

theorem clearMaster_eval (regs : Regs) (master source output payload : List Bool) :
    Eval (clear 12) (2 * master.length + 3)
      (state regs [] [] master source output payload)
      (state (reset regs) [] [] [] source output payload) := by
  have hs : cleared 12 (state regs [] [] master source output payload) =
      state (reset regs) [] [] [] source output payload := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [ state, StackRoutines.clearStacks]
  have h := clear_eval 12 (state regs [] [] master source output payload)
  rw [hs] at h
  simpa [state] using h

abbrev pushFalse (stack : Fin 16) : Cmd 15 16 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push stack 0))

def pushed (stack : Fin 16) (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks stack (false :: d.stacks stack)⟩

theorem pushFalse_eval (stack : Fin 16) (d : Data) : Eval (pushFalse stack) 2 d (pushed stack d) := by
  let middle : Data := ⟨Function.update d.regs 0 false, d.stacks⟩
  have h1 : Eval (RecordPrograms.atom (.set 0 false)) 1 d middle := by
    exact .base (.atom _ _)
  have h2 : Eval (RecordPrograms.atom (.push stack 0)) 1 middle (pushed stack d) := by
    apply Eval.base
    simpa [middle, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 15) (s := 16) stack 0) middle
  exact h1.seq h2

theorem pushOutput_eval (regs : Regs) (master source output payload : List Bool) :
    Eval (pushFalse 14) 2
      (state regs [] [] master source output payload)
      (state (Function.update regs 0 false) [] [] master source (false :: output) payload) := by
  have hs : pushed 14 (state regs [] [] master source output payload) =
      state (Function.update regs 0 false) [] [] master source (false :: output) payload := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [ state]
  simpa only [hs] using pushFalse_eval 14 (state regs [] [] master source output payload)

theorem pushSource_eval (regs : Regs) (master source output payload : List Bool) :
    Eval (pushFalse 13) 2
      (state regs [] [] master source output payload)
      (state (Function.update regs 0 false) [] [] master (false :: source) output payload) := by
  have hs : pushed 13 (state regs [] [] master source output payload) =
      state (Function.update regs 0 false) [] [] master (false :: source) output payload := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [ state]
  simpa only [hs] using pushFalse_eval 13 (state regs [] [] master source output payload)

end SubexponentialSAT.ExecClauseFiltersProgram

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTautologyProgram
import OAI.Algorithms.SubexponentialSAT.ProgramEncoding

namespace OAI.Algorithms

/-!
# Actual tautological-clause filtering

The outer record loop runs the checked clause-tautology machine on each clause,
emits exactly the clauses that it rejects as tautologies, and restores their
original list order. The Boolean predicates below specify this concrete code;
they are not instructions available to the machine.
-/

namespace SubexponentialSAT.SubexpTautologyFilterProgram

open BitProgram StructuredCalls

abbrev Data := State 13 11

def decodeFields : List (List Bool) → Option (List ℕ)
  | [] => some []
  | bits :: rest => do
      let (c, tail) ← Encoding.readNat bits
      if tail.isEmpty then
        let cs ← decodeFields rest
        pure (c :: cs)
      else none

def decodeClause (bits : List Bool) : Option (List ℕ) := do
  let (fields, rest) ← ProgramEncoding.readRecords bits
  if rest.isEmpty then decodeFields fields else none

theorem decodeFields_literalRecords (C : List ℕ) :
    decodeFields (SubexpTautologyProgram.literalRecords C) = some C := by
  induction C with
  | nil => rfl
  | cons c C ih =>
    change decodeFields (C.map Encoding.encodeNat) = some C at ih
    simp [SubexpTautologyProgram.literalRecords, decodeFields, ih]

@[simp] theorem decodeClause_encodedClause (C : List ℕ) :
    decodeClause (SubexpTautologyProgram.encodedClause C) = some C := by
  rw [SubexpTautologyProgram.encodedClause_records]
  change (do
    let (fields, rest) ← ProgramEncoding.readRecords
      (ProgramEncoding.encodeRecords (SubexpTautologyProgram.literalRecords C))
    if rest.isEmpty then decodeFields fields else none) = some C
  simp [decodeFields_literalRecords]

def keepClause (bits : List Bool) : Bool :=
  match decodeClause bits with
  | none => false
  | some C => !(ExecCNF.tautology SubexpFrontend.negateCode C)

@[simp] theorem keepClause_encodedClause (C : List ℕ) :
    keepClause (SubexpTautologyProgram.encodedClause C) =
      !(ExecCNF.tautology SubexpFrontend.negateCode C) := by
  simp [keepClause]

def coreRegister (i : Fin 10) : Fin 13 := Fin.castAdd 3 i
def coreStack (i : Fin 8) : Fin 11 := ⟨i.val + 3, by omega⟩

theorem coreRegister_injective : Function.Injective coreRegister := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 13 => i.val) h)

theorem coreStack_injective : Function.Injective coreStack := by
  intro i j h
  apply Fin.ext
  have he := congrArg (fun i : Fin 11 => i.val) h
  simp only [coreStack] at he
  omega

def coreProgram := ProgramLinking.liftProgram
  SubexpTautologyProgram.program coreRegister coreStack

abbrev coreCall : Cmd 13 11 := .call coreProgram

private theorem embed_restricted {r s R S : ℕ}
    (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (frame : State R S) :
    embedState reg stk frame ⟨frame.regs ∘ reg, frame.stacks ∘ stk⟩ = frame := by
  cases frame with
  | mk regs stackValues =>
    unfold embedState
    congr 1
    · funext i
      by_cases h : ∃ j, reg j = i
      · obtain ⟨j, rfl⟩ := h
        exact hr.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h
    · funext i
      by_cases h : ∃ j, stk j = i
      · obtain ⟨j, rfl⟩ := h
        exact hs.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h

theorem coreCall_eval (C : List ℕ) (d : Data)
    (hsource : d.stacks 3 = SubexpTautologyProgram.encodedClause C)
    (hready : ∀ i : Fin 8, i ≠ 0 → d.stacks (coreStack i) = []) :
    ∃ n ≤ 200 * ((SubexpTautologyProgram.encodedClause C).length + 1) ^ 2,
      ∃ e : Data, Eval coreCall n d e ∧
      e.regs 9 = ExecCNF.tautology SubexpFrontend.negateCode C ∧
      e.stacks 4 = [ExecCNF.tautology SubexpFrontend.negateCode C] ∧
      e.stacks 5 = SubexpTautologyProgram.encodedClause C ∧
      (∀ i : Fin 8, i ≠ 1 → i ≠ 2 → e.stacks (coreStack i) = []) ∧
      (∀ i : Fin 11, i.val < 3 → e.stacks i = d.stacks i) ∧
      (∀ i : Fin 13, 10 ≤ i.val → e.regs i = d.regs i) := by
  let a : SubexpTautologyProgram.Data :=
    ⟨d.regs ∘ coreRegister, d.stacks ∘ coreStack⟩
  have ha0 : a.stacks 0 = SubexpTautologyProgram.encodedClause C := hsource
  have ha : SubexpTautologyProgram.Ready a := hready
  obtain ⟨b, hbreg, hbout, hbclause, hbclear, n, hn, hbtrace⟩ :=
    SubexpTautologyProgram.tautology_runsIn C a ha0 ha
  let e := embedState coreRegister coreStack d b
  have he := eval_call_lifted SubexpTautologyProgram.program coreRegister coreStack d
    coreRegister_injective coreStack_injective hbtrace
  rw [embed_restricted _ _ coreRegister_injective coreStack_injective] at he
  refine ⟨n, hn, e, he, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (embedState_register coreRegister coreStack d b coreRegister_injective 9).trans hbreg
  · exact (embedState_stack coreRegister coreStack d b coreStack_injective 1).trans hbout
  · exact (embedState_stack coreRegister coreStack d b coreStack_injective 2).trans hbclause
  · intro i hi1 hi2
    exact (embedState_stack coreRegister coreStack d b coreStack_injective i).trans
      (hbclear i hi1 hi2)
  · intro i hi
    apply embedState_stack_frame
    rintro ⟨j, hj⟩
    have hval := congrArg (fun i : Fin 11 => i.val) hj
    simp only [coreStack] at hval
    omega
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hval := congrArg (fun i : Fin 13 => i.val) hj
    have hjlt := j.isLt
    simp only [coreRegister, Fin.val_castAdd] at hval
    omega

abbrev transferProgram (source target : Fin 11) : Program 13 11 4 :=
  StackRoutines.transferProgram source target 0 1

def transferred (source target : Fin 11) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks source target d.stacks⟩

abbrev transfer (source target : Fin 11) : Cmd 13 11 := .call (transferProgram source target)

theorem transfer_eval (source target : Fin 11) (hne : source ≠ target) (d : Data) :
    Eval (transfer source target) (3 * (d.stacks source).length + 3)
      d (transferred source target d) := by
  have h := StackRoutines.transferProgram_trace (r := 13) (s := 11) source target 0 1
    hne (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace (transferProgram source target) h 3 rfl rfl
  apply Eval.call
  simpa [transferProgram, StackRoutines.transferResult, transferred,
    StructuredProgram.State.withPC, Nat.add_assoc] using hh

abbrev clearProgram (port : Fin 11) : Program 13 11 3 := StackRoutines.clearProgram port 0 1

def cleared (port : Fin 11) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks port d.stacks⟩

abbrev clear (port : Fin 11) : Cmd 13 11 := .call (clearProgram port)

theorem clear_eval (port : Fin 11) (d : Data) :
    Eval (clear port) (2 * (d.stacks port).length + 3) d (cleared port d) := by
  have h := StackRoutines.clearProgram_trace (r := 13) (s := 11) port 0 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace (clearProgram port) h 2 rfl rfl
  apply Eval.call
  simpa [clearProgram, StackRoutines.clearResult, cleared,
    StructuredProgram.State.withPC, Nat.add_assoc] using hh

def emitRegister (i : Fin 3) : Fin 13 := ⟨i.val + 10, by omega⟩

def emitStack (i : Fin 4) : Fin 11 :=
  match i.val with
  | 0 => 0
  | 1 => 3
  | 2 => 2
  | _ => 1

theorem emitRegister_injective : Function.Injective emitRegister := by
  intro i j h
  apply Fin.ext
  have he := congrArg (fun i : Fin 13 => i.val) h
  simp only [emitRegister] at he
  omega

theorem emitStack_injective : Function.Injective emitStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [emitStack]

def emitProgram := ProgramLinking.liftProgram
  SubexpNormalizeProgram.emitIfSelectedProgram emitRegister emitStack

abbrev emitCall : Cmd 13 11 := .call emitProgram

theorem emitCall_eval (bits : List Bool) (d : Data) (hpayload : d.stacks 1 = bits.reverse) :
    ∃ e : Data,
      Eval emitCall (SubexpNormalizeProgram.emitIfSelectedSteps (d.regs 12) bits + 1) d e ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧
      e.stacks 2 = (if d.regs 12 then true :: (Encoding.frame bits ++ d.stacks 2)
        else d.stacks 2) ∧
      (∀ i : Fin 11, 3 ≤ i.val → e.stacks i = d.stacks i) ∧
      e.regs 10 = false ∧ e.regs 11 = true ∧ e.regs 12 = false := by
  let a := SubexpNormalizeProgram.filterState (d.regs 10) (d.regs 11) (d.regs 12)
    (d.stacks 0) (d.stacks 3) (d.stacks 2) bits.reverse
  let b := SubexpNormalizeProgram.filterState false true false
    (d.stacks 0) (d.stacks 3)
    (if d.regs 12 then true :: (Encoding.frame bits ++ d.stacks 2) else d.stacks 2) []
  have ha : a = ⟨d.regs ∘ emitRegister, d.stacks ∘ emitStack⟩ := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [
        SubexpPostfixControl.quadruple, emitStack, hpayload]
  let e := embedState emitRegister emitStack d b
  have he := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram
    emitRegister emitStack d emitRegister_injective emitStack_injective
    (SubexpNormalizeProgram.emitIfSelected_trace (d.regs 12) bits (d.stacks 0)
      (d.stacks 3) (d.stacks 2) (d.regs 10) (d.regs 11))
  change Eval emitCall (SubexpNormalizeProgram.emitIfSelectedSteps (d.regs 12) bits + 1)
    (embedState emitRegister emitStack d a) e at he
  rw [ha, embed_restricted _ _ emitRegister_injective emitStack_injective] at he
  refine ⟨e, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact embedState_stack emitRegister emitStack d b emitStack_injective 0
  · exact embedState_stack emitRegister emitStack d b emitStack_injective 3
  · exact embedState_stack emitRegister emitStack d b emitStack_injective 2
  · intro i hi
    by_cases h3 : i = 3
    · subst i
      exact embedState_stack emitRegister emitStack d b emitStack_injective 1
    · apply embedState_stack_frame
      rintro ⟨j, hj⟩
      fin_cases j <;> simp [emitStack] at hj <;> subst i <;> omega
  · exact embedState_register emitRegister emitStack d b emitRegister_injective 0
  · exact embedState_register emitRegister emitStack d b emitRegister_injective 1
  · exact embedState_register emitRegister emitStack d b emitRegister_injective 2

def selected (d : Data) : Data :=
  ⟨Function.update d.regs 12 (!(d.regs 9)), d.stacks⟩

theorem select_eval (d : Data) :
    Eval (RecordPrograms.atom (.bnot 12 9)) 1 d (selected d) := by
  have h : (StructuredProgram.Atom.bnot (r := 13) (s := 11) 12 9).eval d = selected d := rfl
  rw [← h]
  exact .base (.atom _ _)

def invariant (d : Data) : Prop := ∀ i : Fin 11, 3 ≤ i.val → d.stacks i = []

abbrev callback : Cmd 13 11 :=
  .seq (transfer 1 3) (.seq coreCall (.seq (transfer 5 1)
    (.seq (clear 4) (.seq (RecordPrograms.atom (.bnot 12 9)) emitCall))))

def perClauseCost (bits : List Bool) : ℕ := 250 * (bits.length + 1) ^ 2

theorem callback_eval (C : List ℕ) (d : Data)
    (hpayload : d.stacks 1 = (SubexpTautologyProgram.encodedClause C).reverse)
    (valid : invariant d) :
    ∃ n ≤ perClauseCost (SubexpTautologyProgram.encodedClause C), ∃ e : Data,
      Eval callback n d e ∧ invariant e ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧
      e.stacks 2 = (if keepClause (SubexpTautologyProgram.encodedClause C) then
        true :: (Encoding.frame (SubexpTautologyProgram.encodedClause C) ++ d.stacks 2)
        else d.stacks 2) ∧
      e.regs 10 = false ∧ e.regs 11 = true ∧ e.regs 12 = false := by
  let a := transferred 1 3 d
  have ha3 : a.stacks 3 = SubexpTautologyProgram.encodedClause C := by
    simp [a, transferred, StackRoutines.transferStacks, hpayload, valid 3 (by decide)]
  have haReady : ∀ i : Fin 8, i ≠ 0 → a.stacks (coreStack i) = [] := by
    intro i hi
    have hv : 0 < i.val := by
      have hn : i.val ≠ 0 := fun h => hi (Fin.ext h)
      omega
    have hneq1 : coreStack i ≠ 1 := by
      intro h
      have := congrArg (fun j : Fin 11 => j.val) h
      simp only [coreStack] at this
      omega
    have hneq3 : coreStack i ≠ 3 := by
      intro h
      have := congrArg (fun j : Fin 11 => j.val) h
      simp only [coreStack] at this
      omega
    simpa [a, transferred, StackRoutines.transferStacks, hneq1, hneq3] using
      valid (coreStack i) (by simp [coreStack])
  obtain ⟨m, hm, b, hcore, hbreg, hb4, hb5, hbclear, hbframe, hbregs⟩ :=
    coreCall_eval C a ha3 haReady
  let c := transferred 5 1 b
  let f := selected (cleared 4 c)
  have hb1 : b.stacks 1 = [] := by
    simpa [a, transferred, StackRoutines.transferStacks] using hbframe 1 (by decide)
  have hc1 : c.stacks 1 = (SubexpTautologyProgram.encodedClause C).reverse := by
    simp [c, transferred, StackRoutines.transferStacks, hb1, hb5]
  have hc4 : c.stacks 4 = [ExecCNF.tautology SubexpFrontend.negateCode C] := by
    simpa [c, transferred, StackRoutines.transferStacks] using hb4
  have hf1 : f.stacks 1 = (SubexpTautologyProgram.encodedClause C).reverse := by
    simpa [f, selected, cleared, StackRoutines.clearStacks] using hc1
  have hf12 : f.regs 12 = !(ExecCNF.tautology SubexpFrontend.negateCode C) := by
    simp [f, selected, cleared, transferred, c, readRegs, hbreg]
  have hf0 : f.stacks 0 = d.stacks 0 := by
    simpa [f, selected, cleared, c, transferred, StackRoutines.clearStacks,
      StackRoutines.transferStacks, a] using hbframe 0 (by decide)
  have hf2 : f.stacks 2 = d.stacks 2 := by
    simpa [f, selected, cleared, c, transferred, StackRoutines.clearStacks,
      StackRoutines.transferStacks, a] using hbframe 2 (by decide)
  have hvalidf : invariant f := by
    intro i hi
    fin_cases i
    · simp at hi
    · simp at hi
    · simp at hi
    · simpa [f, selected, cleared, c, transferred, StackRoutines.clearStacks,
        StackRoutines.transferStacks, coreStack] using hbclear 0 (by decide) (by decide)
    · simp [f, selected, cleared, StackRoutines.clearStacks]
    · simp [f, selected, cleared, c, transferred, StackRoutines.clearStacks,
        StackRoutines.transferStacks]
    · simpa [f, selected, cleared, c, transferred, StackRoutines.clearStacks,
        StackRoutines.transferStacks, coreStack] using hbclear 3 (by decide) (by decide)
    · simpa [f, selected, cleared, c, transferred, StackRoutines.clearStacks,
        StackRoutines.transferStacks, coreStack] using hbclear 4 (by decide) (by decide)
    · simpa [f, selected, cleared, c, transferred, StackRoutines.clearStacks,
        StackRoutines.transferStacks, coreStack] using hbclear 5 (by decide) (by decide)
    · simpa [f, selected, cleared, c, transferred, StackRoutines.clearStacks,
        StackRoutines.transferStacks, coreStack] using hbclear 6 (by decide) (by decide)
    · simpa [f, selected, cleared, c, transferred, StackRoutines.clearStacks,
        StackRoutines.transferStacks, coreStack] using hbclear 7 (by decide) (by decide)
  obtain ⟨e, hemit, he0, he1, he2, heframe, he10, he11, he12⟩ :=
    emitCall_eval (SubexpTautologyProgram.encodedClause C) f hf1
  let n := (3 * (d.stacks 1).length + 3) +
    (m + ((3 * (b.stacks 5).length + 3) +
      ((2 * (c.stacks 4).length + 3) +
        (1 + (SubexpNormalizeProgram.emitIfSelectedSteps (f.regs 12)
          (SubexpTautologyProgram.encodedClause C) + 1)))))
  refine ⟨n, ?_, e, ?_, ?_, he0.trans hf0, he1, ?_, he10, he11, he12⟩
  · have hecost := SubexpNormalizeProgram.emitIfSelected_steps_le (f.regs 12)
      (SubexpTautologyProgram.encodedClause C)
    dsimp [n, perClauseCost]
    rw [hpayload, hb5, hc4]
    simp only [List.length_reverse, List.length_cons, List.length_nil]
    have hsquare : (SubexpTautologyProgram.encodedClause C).length + 1 ≤
        ((SubexpTautologyProgram.encodedClause C).length + 1) ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_right _ (by omega)
    have hslack : 11 * (SubexpTautologyProgram.encodedClause C).length + 24 ≤
        50 * ((SubexpTautologyProgram.encodedClause C).length + 1) ^ 2 := by
      calc
        11 * (SubexpTautologyProgram.encodedClause C).length + 24 ≤
            50 * ((SubexpTautologyProgram.encodedClause C).length + 1) := by omega
        _ ≤ 50 * ((SubexpTautologyProgram.encodedClause C).length + 1) ^ 2 :=
          Nat.mul_le_mul_left 50 hsquare
    omega
  · exact (transfer_eval 1 3 (by decide) d).seq
      (hcore.seq ((transfer_eval 5 1 (by decide) b).seq
        ((clear_eval 4 c).seq ((select_eval (cleared 4 c)).seq hemit))))
  · intro i hi
    exact (heframe i hi).trans (hvalidf i hi)
  · simpa [hf12, hf2] using he2

def ports : RecordPrograms.Ports 13 11 where
  tag := 10
  present := 11
  found := 12
  source := 0
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def ClausePayload (bits : List Bool) : Prop :=
  ∃ C : List ℕ, bits = SubexpTautologyProgram.encodedClause C

theorem callback_contract :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      perClauseCost invariant (SubexpNormalizeProgram.FilterEffect 2 keepClause) ClausePayload := by
  intro bits tail base hbits hbase
  obtain ⟨C, rfl⟩ := hbits
  let d := RecordPrograms.state ports base false true false tail
    (SubexpTautologyProgram.encodedClause C).reverse
  have hd1 : d.stacks 1 = (SubexpTautologyProgram.encodedClause C).reverse := by
    simp [d, RecordPrograms.state, ports]
  have hd0 : d.stacks 0 = tail := by simp [d, RecordPrograms.state, ports]
  have hd2 : d.stacks 2 = base.stacks 2 := by simp [d, RecordPrograms.state, ports]
  have hdvalid : invariant d := by
    intro i hi
    have h0 : i ≠ 0 := by intro h; subst i; omega
    have h1 : i ≠ 1 := by intro h; subst i; omega
    simpa [d, RecordPrograms.state, ports, h0, h1] using hbase i hi
  obtain ⟨n, hn, e, he, hv, he0, he1, he2, he10, he11, he12⟩ :=
    callback_eval C d hd1 hdvalid
  have heState : RecordPrograms.state ports e false true false tail [] = e :=
    RecordPrograms.state_eq_self ports e _ _ _ _ _ he10 he11 he12 (he0.trans hd0) he1
  refine ⟨n, e, hn, hv, ?_, ?_⟩
  · simpa [SubexpNormalizeProgram.FilterEffect, hd2] using he2
  · rw [heState]
    exact he

def formulaRecords (F : List (List ℕ)) : List (List Bool) :=
  F.map SubexpTautologyProgram.encodedClause

def encodedFormula (F : List (List ℕ)) : List Bool :=
  Encoding.encodeList SubexpTautologyProgram.encodedClause F

theorem encodedFormula_records (F : List (List ℕ)) :
    encodedFormula F = Encoding.encodeList id (formulaRecords F) := by
  induction F with
  | nil => rfl
  | cons C F ih => simpa [encodedFormula, formulaRecords, Encoding.encodeList] using ih

theorem valid_formulaRecords (F : List (List ℕ)) :
    ∀ bits ∈ formulaRecords F, ClausePayload bits := by
  intro bits hb
  obtain ⟨C, _, rfl⟩ := List.mem_map.mp hb
  exact ⟨C, rfl⟩

theorem filtered_formulaRecords (F : List (List ℕ)) :
    (formulaRecords F).filter keepClause =
      formulaRecords (ExecCNF.removeTautologies SubexpFrontend.negateCode F) := by
  change (F.map SubexpTautologyProgram.encodedClause).filter keepClause =
    (F.filter (fun C => !(ExecCNF.tautology SubexpFrontend.negateCode C))).map
      SubexpTautologyProgram.encodedClause
  induction F with
  | nil => rfl
  | cons C F ih =>
    cases h : !(ExecCNF.tautology SubexpFrontend.negateCode C) <;>
      simp [ h, ih]

theorem filter_budget_le (records : List (List Bool)) :
    3 + RecordPrograms.budget perClauseCost records ≤
      300 * ((Encoding.encodeList id records).length + 1) ^ 2 := by
  induction records with
  | nil => simp [RecordPrograms.budget, Encoding.encodeList]
  | cons bits records ih =>
    simp only [RecordPrograms.budget, perClauseCost, Encoding.length_encodeList_cons, id_eq]
    have hproduct : 0 ≤ bits.length * (Encoding.encodeList id records).length := Nat.zero_le _
    nlinarith

theorem encoded_filter_length_le (records : List (List Bool)) :
    (Encoding.encodeList id (records.filter keepClause)).length ≤
      (Encoding.encodeList id records).length := by
  induction records with
  | nil => rfl
  | cons bits records ih =>
    cases h : keepClause bits <;>
      simp [ h, Encoding.length_encodeList_cons] <;> omega

theorem encoded_reverse_length (records : List (List Bool)) :
    (Encoding.encodeList id records.reverse).length = (Encoding.encodeList id records).length := by
  change (ProgramEncoding.encodeRecords records.reverse).length =
    (ProgramEncoding.encodeRecords records).length
  simp [ProgramEncoding.encodeRecords_length, List.map_reverse]

abbrev scan : Cmd 13 11 := RecordPrograms.iterate ports callback

theorem scan_eval (records acc : List (List Bool)) (d : Data)
    (valid : invariant d) (hacc : d.stacks 2 = Encoding.encodeList id acc)
    (hrecords : ∀ bits ∈ records, ClausePayload bits) (v p f : Bool) :
    ∃ n ≤ 300 * ((Encoding.encodeList id records).length + 1) ^ 2, ∃ next : Data,
      invariant next ∧
      next.stacks 2 = Encoding.encodeList id ((records.filter keepClause).reverse ++ acc) ∧
      Eval scan n
        (RecordPrograms.state ports d v p f (Encoding.encodeList id records) [])
        (RecordPrograms.state ports next false true false [] []) := by
  obtain ⟨n, next, hn, hnext, hhistory, he⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) perClauseCost invariant
    (SubexpNormalizeProgram.FilterEffect 2 keepClause) ClausePayload callback_contract
    records [] d hrecords valid v p f
  have hout := SubexpNormalizeProgram.filterVisits_result 2 keepClause hhistory acc hacc
  have hany : records.any (fun _ => false) = false := by
    induction records <;> simp_all
  exact ⟨n, hn.trans (filter_budget_le records), next, hnext, hout,
    by simpa [scan, hany, SubexpNormalizeProgram.unread_false] using he⟩

def reverseStack (i : Fin 4) : Fin 11 :=
  if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 0 else 1

theorem reverseStack_injective : Function.Injective reverseStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [reverseStack]

def reverseProgram := ProgramLinking.liftProgram
  SubexpNormalizeProgram.reverseRecordsProgram emitRegister reverseStack

abbrev reverseCall : Cmd 13 11 := .call reverseProgram

theorem reverseCall_eval (records acc : List (List Bool)) (d : Data)
    (hsource : d.stacks 2 = Encoding.encodeList id records)
    (houtput : d.stacks 0 = Encoding.encodeList id acc) (hpayload : d.stacks 1 = []) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length, ∃ e : Data,
      Eval reverseCall n d e ∧
      e.stacks 0 = Encoding.encodeList id (records.reverse ++ acc) ∧
      e.stacks 1 = [] ∧ e.stacks 2 = [] ∧
      (∀ i : Fin 11, 3 ≤ i.val → e.stacks i = d.stacks i) := by
  let a : State 3 4 := ⟨d.regs ∘ emitRegister, d.stacks ∘ reverseStack⟩
  have ha : a = SubexpNormalizeProgram.filterState (d.regs 10) (d.regs 11) (d.regs 12)
      (Encoding.encodeList id records) (d.stacks 3) (Encoding.encodeList id acc) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ emitRegister ]
    · funext i
      fin_cases i <;> simp [ reverseStack,
        hsource, houtput, hpayload]
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records acc []
    (d.stacks 3) (d.regs 10) (d.regs 11) (d.regs 12)
  simp only [List.append_nil] at ht
  rw [← ha] at ht
  have he := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram
    emitRegister reverseStack d emitRegister_injective reverseStack_injective ht
  rw [embed_restricted _ _ emitRegister_injective reverseStack_injective] at he
  let b := SubexpNormalizeProgram.filterState false true false [] (d.stacks 3)
    (Encoding.encodeList id (records.reverse ++ acc)) []
  let e := embedState emitRegister reverseStack d b
  have hstack (i : Fin 4) : e.stacks (reverseStack i) = b.stacks i :=
    embedState_stack _ _ _ _ reverseStack_injective i
  refine ⟨n, hn, e, he, ?_, ?_, ?_, ?_⟩
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 2
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 3
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 0
  · intro i hi
    by_cases h3 : i = 3
    · subst i
      simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 1
    · apply embedState_stack_frame
      rintro ⟨j, hj⟩
      fin_cases j <;> simp [reverseStack] at hj <;> subst i <;> omega

abbrev pushFalse (stack : Fin 11) : Cmd 13 11 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push stack 0))

def pushed (stack : Fin 11) (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks stack (false :: d.stacks stack)⟩

theorem pushFalse_eval (stack : Fin 11) (d : Data) : Eval (pushFalse stack) 2 d (pushed stack d) := by
  let middle : Data := ⟨Function.update d.regs 0 false, d.stacks⟩
  have h1 : Eval (RecordPrograms.atom (.set 0 false)) 1 d middle := by
    apply Eval.base
    simpa [middle, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.set (r := 13) (s := 11) 0 false) d
  have h2 : Eval (RecordPrograms.atom (.push stack 0)) 1 middle (pushed stack d) := by
    apply Eval.base
    simpa [middle, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 13) (s := 11) stack 0) middle
  exact Eval.seq h1 h2

abbrev filter : Cmd 13 11 := .seq (pushFalse 2) (.seq scan (.seq (pushFalse 0) reverseCall))

def Ready (d : Data) : Prop := invariant d ∧ d.stacks 1 = [] ∧ d.stacks 2 = []

theorem ready_iff (d : Data) : Ready d ↔ ∀ i : Fin 11, i ≠ 0 → d.stacks i = [] := by
  constructor
  · rintro ⟨hc, h1, h2⟩ i hi
    fin_cases i
    · exact (hi rfl).elim
    · exact h1
    · exact h2
    · exact hc 3 (by decide)
    · exact hc 4 (by decide)
    · exact hc 5 (by decide)
    · exact hc 6 (by decide)
    · exact hc 7 (by decide)
    · exact hc 8 (by decide)
    · exact hc 9 (by decide)
    · exact hc 10 (by decide)
  · intro h
    refine ⟨?_, h 1 (by decide), h 2 (by decide)⟩
    intro i hi
    apply h i
    intro he
    subst i
    contradiction

theorem filter_eval (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 0 = encodedFormula F) (hready : Ready d) :
    ∃ n ≤ 399 * ((encodedFormula F).length + 1) ^ 2, ∃ e : Data,
      Eval filter n d e ∧ Ready e ∧
      e.stacks 0 = encodedFormula (ExecCNF.removeTautologies SubexpFrontend.negateCode F) := by
  rcases hready with ⟨hvalid, hpayload, houtput⟩
  let a := pushed 2 d
  have ha : invariant a := by
    intro i hi
    have hne : i ≠ 2 := by intro h; subst i; omega
    simpa [a, pushed, hne] using hvalid i hi
  have ha2 : a.stacks 2 = Encoding.encodeList id [] := by
    simp [a, pushed, houtput, Encoding.encodeList]
  obtain ⟨n, hn, next, hnext, hout, hscan⟩ := scan_eval (formulaRecords F) [] a ha ha2
    (valid_formulaRecords F) (a.regs 10) (a.regs 11) (a.regs 12)
  have hstart : RecordPrograms.state ports a (a.regs 10) (a.regs 11) (a.regs 12)
      (Encoding.encodeList id (formulaRecords F)) [] = a :=
    RecordPrograms.state_eq_self ports a _ _ _ _ _ rfl rfl rfl
      (by
        change Function.update d.stacks 2 (false :: d.stacks 2) ports.source =
          Encoding.encodeList id (formulaRecords F)
        rw [show ports.source = (0 : Fin 11) from rfl]
        simpa [← encodedFormula_records] using hsource)
      (by
        change Function.update d.stacks 2 (false :: d.stacks 2) ports.payload = []
        rw [show ports.payload = (1 : Fin 11) from rfl]
        simpa using hpayload)
  rw [hstart] at hscan
  let b := RecordPrograms.state ports next false true false [] []
  let c := pushed 0 b
  have hcvalid : invariant c := by
    intro i hi
    have h0 : i ≠ 0 := by intro h; subst i; omega
    have h1 : i ≠ 1 := by intro h; subst i; omega
    simpa [c, pushed, b, RecordPrograms.state, ports, h0, h1] using hnext i hi
  have hc2 : c.stacks 2 =
      Encoding.encodeList id ((formulaRecords F).filter keepClause).reverse := by
    simpa [c, pushed, b, RecordPrograms.state, ports] using hout
  have hc0 : c.stacks 0 = Encoding.encodeList id [] := by
    simp [c, pushed, b, RecordPrograms.state, ports, Encoding.encodeList]
  have hc1 : c.stacks 1 = [] := by simp [c, pushed, b, RecordPrograms.state, ports]
  obtain ⟨m, hm, e, hreverse, he0, he1, he2, heframe⟩ :=
    reverseCall_eval ((formulaRecords F).filter keepClause).reverse [] c hc2 hc0 hc1
  have hfilterlen := encoded_filter_length_le (formulaRecords F)
  rw [encoded_reverse_length] at hm
  refine ⟨2 + (n + (2 + m)), ?_, e, ?_, ?_, ?_⟩
  · rw [← encodedFormula_records] at hn hfilterlen
    nlinarith
  · exact (pushFalse_eval 2 d).seq (hscan.seq ((pushFalse_eval 0 b).seq hreverse))
  · refine ⟨?_, he1, he2⟩
    intro i hi
    exact (heframe i hi).trans (hcvalid i hi)
  · simpa [filtered_formulaRecords, ← encodedFormula_records] using he0

def program := compiled filter 0 0

theorem filter_runsIn (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 0 = encodedFormula F) (hready : Ready d) :
    ∃ e : Data, Ready e ∧
      e.stacks 0 = encodedFormula (ExecCNF.removeTautologies SubexpFrontend.negateCode F) ∧
      RunsIn program (400 * ((encodedFormula F).length + 1) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨n, hn, e, he, hready', hout⟩ := filter_eval F d hsource hready
  refine ⟨e, hready', hout, n + 1, ?_, compiled_halt_trace he 0 0⟩
  have hpos : 0 < ((encodedFormula F).length + 1) ^ 2 := pow_pos (by omega) _
  omega

theorem filtered_length_le (F : List (List ℕ)) :
    (encodedFormula (ExecCNF.removeTautologies SubexpFrontend.negateCode F)).length ≤
      (encodedFormula F).length := by
  rw [encodedFormula_records, ← filtered_formulaRecords, encodedFormula_records]
  exact encoded_filter_length_le _

def inputData (bits : List Bool) : Data :=
  ⟨fun _ => false, fun i => if i = 0 then bits else []⟩

theorem inputData_ready (bits : List Bool) : Ready (inputData bits) := by
  apply (ready_iff _).mpr
  intro i hi
  simp [inputData, hi]

theorem initial_eq_inputData (bits : List Bool) :
    initial program bits = (inputData bits).withPC (some program.entry) := rfl

/-- This starts with the actual raw encoded formula and empty work stacks. -/
theorem raw_input_runsIn (F : List (List ℕ)) :
    ∃ e : Data, Ready e ∧
      e.stacks 0 = encodedFormula (ExecCNF.removeTautologies SubexpFrontend.negateCode F) ∧
      RunsIn program (400 * ((encodedFormula F).length + 1) ^ 2)
        (initial program (encodedFormula F)) (e.withPC none) := by
  obtain ⟨e, he, hout, hrun⟩ := filter_runsIn F (inputData (encodedFormula F))
    (by simp [inputData]) (inputData_ready _)
  exact ⟨e, he, hout, by simpa only [initial_eq_inputData] using hrun⟩

/-- The finite-control execution compiles to an actual primitive tape trace. -/
theorem filter_primitive_execution (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 0 = encodedFormula F) (hready : Ready d) :
    ∃ e : Data, Ready e ∧
      e.stacks 0 = encodedFormula (ExecCNF.removeTautologies SubexpFrontend.negateCode F) ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (400 * ((encodedFormula F).length + 1) ^ 2))
        (primitiveCfg program (d.withPC (some program.entry)))
        (primitiveCfg program (e.withPC none)) := by
  obtain ⟨e, he, hout, hrun⟩ := filter_runsIn F d hsource hready
  exact ⟨e, he, hout, primitive_execution program hrun⟩

theorem raw_input_primitive (F : List (List ℕ)) :
    ∃ e : Data, Ready e ∧
      e.stacks 0 = encodedFormula (ExecCNF.removeTautologies SubexpFrontend.negateCode F) ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (400 * ((encodedFormula F).length + 1) ^ 2))
        ((primitive program).init (encodedFormula F))
        (primitiveCfg program (e.withPC none)) := by
  obtain ⟨e, he, hout, hrun⟩ := raw_input_runsIn F
  exact ⟨e, he, hout, by simpa only [primitive_initial] using primitive_execution program hrun⟩

end SubexponentialSAT.SubexpTautologyFilterProgram

end OAI.Algorithms

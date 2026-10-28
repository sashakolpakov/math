import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecLiteralDedupProgram

namespace OAI.Algorithms

/-!
# Actual clausewise literal cleanup

Each framed clause is decoded, passed to the fixed literal-deduplication
program, and framed again. An outer record reversal restores clause order.
The finite control is independent of the input formula and its clause sizes.
-/

namespace SubexponentialSAT.ExecCleanLiteralsProgram

open BitProgram StructuredCalls

abbrev Data := State 13 11
def clauseCode (clause : List ℕ) : List Bool := Encoding.encodeList Encoding.encodeNat clause
def formulaCode (formula : List (List ℕ)) : List Bool := Encoding.encodeList clauseCode formula

def bankReg (i : Fin 10) : Fin 13 := Fin.castAdd 3 i
def bankStack (i : Fin 8) : Fin 11 := Fin.natAdd 3 i

theorem bankReg_injective : Function.Injective bankReg := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 13 => x.val) h

theorem bankStack_injective : Function.Injective bankStack := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun x : Fin 11 => x.val) h
  simpa [bankStack] using hv

@[simp] theorem bankStack_zero : bankStack 0 = 3 := rfl
@[simp] theorem bankStack_eq_zero (i : Fin 8) : bankStack i = 3 ↔ i = 0 := by
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp [bankStack] at hv
    omega
  · rintro rfl
    rfl

@[simp] theorem bankStack_ne_zero (i : Fin 8) : bankStack i ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  simp [bankStack] at hv

@[simp] theorem bankStack_ne_one (i : Fin 8) : bankStack i ≠ 1 := by
  intro h
  have hv := congrArg Fin.val h
  simp [bankStack] at hv
  omega

@[simp] theorem bankStack_ne_two (i : Fin 8) : bankStack i ≠ 2 := by
  intro h
  have hv := congrArg Fin.val h
  simp [bankStack] at hv
  omega

def Clean (d : Data) : Prop := ∀ i : Fin 8, d.stacks (bankStack i) = []

private theorem embed_restricted {r s R S : ℕ}
    (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk) (frame : State R S) :
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

def literalProgram := ProgramLinking.liftProgram
  ExecLiteralDedupProgram.dedupProgram bankReg bankStack
abbrev literalCall : Cmd 13 11 := .call literalProgram

theorem literalCall_eval (clause : List ℕ) (d : Data)
    (hsource : d.stacks 3 = clauseCode clause)
    (hwork : ∀ i : Fin 8, i ≠ 0 → d.stacks (bankStack i) = []) :
    ∃ n ≤ 120 * ((clauseCode clause).length + 1) ^ 2, ∃ e : Data,
      Eval literalCall n d e ∧ e.stacks 3 = clauseCode (ExecCNF.dedupLiterals clause) ∧
      (∀ i : Fin 8, i ≠ 0 → e.stacks (bankStack i) = []) ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = d.stacks 1 ∧ e.stacks 2 = d.stacks 2 ∧
      e.regs 10 = d.regs 10 ∧ e.regs 11 = d.regs 11 ∧ e.regs 12 = d.regs 12 := by
  let a : State 10 8 := ⟨d.regs ∘ bankReg, d.stacks ∘ bankStack⟩
  have ha : ExecLiteralDedupProgram.Ready a := by
    exact ⟨⟨hwork 3 (by decide), hwork 4 (by decide), hwork 5 (by decide),
      hwork 6 (by decide), hwork 7 (by decide)⟩, hwork 1 (by decide), hwork 2 (by decide)⟩
  obtain ⟨next, hnext, hout, n, hn, ht⟩ :=
    ExecLiteralDedupProgram.literal_runsIn clause a hsource ha
  have he := eval_call_lifted ExecLiteralDedupProgram.dedupProgram
    bankReg bankStack d bankReg_injective bankStack_injective ht
  rw [embed_restricted bankReg bankStack bankReg_injective bankStack_injective d] at he
  let e := embedState bankReg bankStack d next
  have hs (i : Fin 8) : e.stacks (bankStack i) = next.stacks i :=
    embedState_stack _ _ _ _ bankStack_injective i
  refine ⟨n, hn, e, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [clauseCode] using (hs 0).trans hout
  · intro i hi
    rw [hs]
    rcases hnext with ⟨⟨h3, h4, h5, h6, h7⟩, h1, h2⟩
    fin_cases i <;> simp_all
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)

abbrev transfer (src dst : Fin 11) : Cmd 13 11 := .call (StackRoutines.transferProgram src dst 0 1)
def transferred (src dst : Fin 11) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

theorem transfer_eval (src dst : Fin 11) (hsd : src ≠ dst) (d : Data) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (transferred src dst d) := by
  apply Eval.call
  simpa [transferred, StructuredProgram.State.withPC] using
    ListRegisterProgram.transfer_run (r := 13) (s := 11) src dst 0 1 hsd (by decide) d.regs d.stacks

def emitReg (i : Fin 3) : Fin 13 := Fin.natAdd 10 i
def emitStack (i : Fin 4) : Fin 11 :=
  if i = 0 then 0 else if i = 1 then 10 else if i = 2 then 2 else 1

theorem emitReg_injective : Function.Injective emitReg := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun x : Fin 13 => x.val) h
  simpa [emitReg] using hv

theorem emitStack_injective : Function.Injective emitStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [emitStack]

def emitProgram := ProgramLinking.liftProgram
  SubexpNormalizeProgram.emitIfSelectedProgram emitReg emitStack
abbrev emitCall : Cmd 13 11 := .call emitProgram

theorem emitCall_eval (bits : List Bool) (d : Data)
    (hquery : d.stacks 1 = bits.reverse) (hselected : d.regs 12 = true) :
    ∃ e : Data, Eval emitCall (SubexpNormalizeProgram.emitIfSelectedSteps true bits + 1) d e ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧
      e.stacks 2 = true :: (Encoding.frame bits ++ d.stacks 2) ∧
      (∀ i : Fin 8, e.stacks (bankStack i) = d.stacks (bankStack i)) ∧
      e.regs 10 = false ∧ e.regs 11 = true ∧ e.regs 12 = false := by
  let a : State 3 4 := ⟨d.regs ∘ emitReg, d.stacks ∘ emitStack⟩
  have ha : a = SubexpNormalizeProgram.filterState (d.regs 10) (d.regs 11) true
      (d.stacks 0) (d.stacks 10) (d.stacks 2) bits.reverse := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ emitReg, hselected]
    · funext i
      fin_cases i <;> simp [ emitStack, hquery]
  have ht := SubexpNormalizeProgram.emitIfSelected_trace true bits
    (d.stacks 0) (d.stacks 10) (d.stacks 2) (d.regs 10) (d.regs 11)
  rw [← ha] at ht
  have he := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram
    emitReg emitStack d emitReg_injective emitStack_injective ht
  rw [embed_restricted emitReg emitStack emitReg_injective emitStack_injective d] at he
  let b := SubexpNormalizeProgram.filterState false true false
    (d.stacks 0) (d.stacks 10) (true :: (Encoding.frame bits ++ d.stacks 2)) []
  let e := embedState emitReg emitStack d b
  have hs (i : Fin 4) : e.stacks (emitStack i) = b.stacks i :=
    embedState_stack _ _ _ _ emitStack_injective i
  have hr (i : Fin 3) : e.regs (emitReg i) = b.regs i :=
    embedState_register _ _ _ _ emitReg_injective i
  refine ⟨e, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [emitStack, b, SubexpNormalizeProgram.filterState] using hs 0
  · simpa [emitStack, b, SubexpNormalizeProgram.filterState] using hs 3
  · simpa [emitStack, b, SubexpNormalizeProgram.filterState] using hs 2
  · intro i
    by_cases hi : i = 7
    · subst i
      simpa [emitStack, bankStack, b, SubexpNormalizeProgram.filterState] using hs 1
    · apply embedState_stack_frame
      intro h
      rcases h with ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have hi' : i.val ≠ 7 := fun h => hi (Fin.ext h)
      fin_cases j <;> simp [emitStack, bankStack] at hv <;> omega
  · simpa [emitReg, b, SubexpNormalizeProgram.filterState] using hr 0
  · simpa [emitReg, b, SubexpNormalizeProgram.filterState] using hr 1
  · simpa [emitReg, b, SubexpNormalizeProgram.filterState] using hr 2

abbrev select : Cmd 13 11 := RecordPrograms.atom (.set 12 true)
def selected (d : Data) : Data := ⟨Function.update d.regs 12 true, d.stacks⟩

theorem select_eval (d : Data) : Eval select 1 d (selected d) := by
  apply Eval.base
  simpa [selected, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
    StructuredProgram.Eval.atom (StructuredProgram.Atom.set (r := 13) (s := 11) 12 true) d

abbrev callback : Cmd 13 11 :=
  .seq (transfer 1 3) (.seq literalCall (.seq (transfer 3 1) (.seq select emitCall)))

theorem clauseCode_dedup_length_le (clause : List ℕ) :
    (clauseCode (ExecCNF.dedupLiterals clause)).length ≤ (clauseCode clause).length := by
  have h := ExecLiteralDedupProgram.encoded_dedup_length_le (clause.map Encoding.encodeNat)
  rw [ExecLiteralDedupProgram.dedup_map Encoding.encodeNat Encoding.encodeNat_injective,
    ExecLiteralDedupProgram.encode_nat_records, ExecLiteralDedupProgram.encode_nat_records] at h
  exact h

theorem callback_eval (clause : List ℕ) (d : Data)
    (hquery : d.stacks 1 = (clauseCode clause).reverse) (hclean : Clean d) :
    ∃ n ≤ 160 * ((clauseCode clause).length + 1) ^ 2, ∃ e : Data,
      Eval callback n d e ∧ Clean e ∧ e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧
      e.stacks 2 = true :: (Encoding.frame (clauseCode (ExecCNF.dedupLiterals clause)) ++ d.stacks 2) ∧
      e.regs 10 = false ∧ e.regs 11 = true ∧ e.regs 12 = false := by
  let a := transferred 1 3 d
  have hd3 : d.stacks 3 = [] := by simpa using hclean 0
  have ha3 : a.stacks 3 = clauseCode clause := by
    simp [a, transferred, StackRoutines.transferStacks, hquery, hd3]
  have haw : ∀ i : Fin 8, i ≠ 0 → a.stacks (bankStack i) = [] := by
    intro i hi
    simp [a, transferred, StackRoutines.transferStacks, hi, hclean i]
  obtain ⟨m, hm, e, he, he3, hew, he0, he1, he2, he10, he11, he12⟩ :=
    literalCall_eval clause a ha3 haw
  let b := transferred 3 1 e
  have hb : Clean b := by
    intro i
    by_cases hi : i = 0
    · subst i
      simp [b, transferred, StackRoutines.transferStacks]
    · simp [b, transferred, StackRoutines.transferStacks, hi, hew i hi]
  have hb1 : b.stacks 1 = (clauseCode (ExecCNF.dedupLiterals clause)).reverse := by
    simp [b, transferred, StackRoutines.transferStacks, he3, he1, a]
  let c := selected b
  obtain ⟨f, hf, hf0, hf1, hf2, hfw, hf10, hf11, hf12⟩ :=
    emitCall_eval (clauseCode (ExecCNF.dedupLiterals clause)) c hb1 (by simp [c, selected])
  let steps := (3 * (d.stacks 1).length + 3) +
    (m + ((3 * (e.stacks 3).length + 3) +
      (1 + (SubexpNormalizeProgram.emitIfSelectedSteps true
        (clauseCode (ExecCNF.dedupLiterals clause)) + 1))))
  have hlen := clauseCode_dedup_length_le clause
  refine ⟨steps, ?_, f, ?_, ?_, ?_, hf1, ?_, hf10, hf11, hf12⟩
  · dsimp [steps]
    rw [hquery, List.length_reverse, he3]
    simp only [SubexpNormalizeProgram.emitIfSelectedSteps, ite_true]
    have hquad : 11 * (clauseCode clause).length + 19 ≤
        40 * ((clauseCode clause).length + 1) ^ 2 := by
      nlinarith only [Nat.zero_le (clauseCode clause).length]
    omega
  · exact Eval.seq (transfer_eval 1 3 (by decide) d) (Eval.seq he
      (Eval.seq (transfer_eval 3 1 (by decide) e) (Eval.seq (select_eval b) hf)))
  · intro i
    exact (hfw i).trans (hb i)
  · simpa [c, selected, b, transferred, StackRoutines.transferStacks, he0, a] using hf0
  · simpa [c, selected, b, transferred, StackRoutines.transferStacks, he2, a] using hf2

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

@[simp] theorem clean_state (base : Data) (v pr f : Bool) (src payload : List Bool) :
    Clean (RecordPrograms.state ports base v pr f src payload) ↔ Clean base := by
  simp [Clean, RecordPrograms.state, ports]

@[simp] theorem state_output (base : Data) (v pr f : Bool) (src payload : List Bool) :
    (RecordPrograms.state ports base v pr f src payload).stacks 2 = base.stacks 2 := by
  simp [RecordPrograms.state, ports]

theorem callback_state_eval (clause : List ℕ) (tail : List Bool) (base : Data) (valid : Clean base) :
    ∃ (n : ℕ) (next : Data), n ≤ 160 * ((clauseCode clause).length + 1) ^ 2 ∧ Clean next ∧
      next.stacks 2 = true :: (Encoding.frame (clauseCode (ExecCNF.dedupLiterals clause)) ++ base.stacks 2) ∧
      Eval callback n
        (RecordPrograms.state ports base false true false tail (clauseCode clause).reverse)
        (RecordPrograms.state ports next false true false tail []) := by
  let d := RecordPrograms.state ports base false true false tail (clauseCode clause).reverse
  obtain ⟨n, hn, next, he, hclean, hs, hp, ho, ht, hpr, hf⟩ :=
    callback_eval clause d (by simp [d, RecordPrograms.state, ports])
      ((clean_state _ _ _ _ _ _).mpr valid)
  have hs' : next.stacks 0 = tail := by simpa [d, RecordPrograms.state, ports] using hs
  have hend : RecordPrograms.state ports next false true false tail [] = next :=
    RecordPrograms.state_eq_self ports next false true false _ [] ht hpr hf hs' hp
  refine ⟨n, next, hn, hclean, ?_, ?_⟩
  · simpa [d] using ho
  · rw [hend]
    exact he

def budget : List (List ℕ) → ℕ
  | [] => 0
  | clause :: rest => 6 * (clauseCode clause).length +
      160 * ((clauseCode clause).length + 1) ^ 2 + 7 + budget rest

theorem formulaCode_eq_records (formula : List (List ℕ)) :
    formulaCode formula = Encoding.encodeList id (formula.map clauseCode) := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      exact congrArg (fun tail => true :: (Encoding.frame (clauseCode clause) ++ tail)) ih

theorem loop_run (formula : List (List ℕ)) (acc : List (List Bool)) (base : Data)
    (valid : Clean base) (hacc : base.stacks 2 = Encoding.encodeList id acc) :
    ∃ (n : ℕ) (next : Data), n ≤ 1 + budget formula ∧ Clean next ∧
      next.stacks 2 = Encoding.encodeList id (((ExecCNF.cleanLiterals formula).map clauseCode).reverse ++ acc) ∧
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports base (formula.map clauseCode) [])
        (RecordPrograms.state ports next false true false [] []) := by
  induction formula generalizing base acc with
  | nil =>
      refine ⟨1, base, by simp [budget], valid, ?_, ?_⟩
      · simpa [ExecCNF.cleanLiterals] using hacc
      · apply Eval.while_false
        simp [RecordPrograms.afterTag]
  | cons clause rest ih =>
      obtain ⟨n, middle, hn, hmiddle, hout, hc⟩ :=
        callback_state_eval clause (Encoding.encodeList id (rest.map clauseCode)) base valid
      let acc' := clauseCode (ExecCNF.dedupLiterals clause) :: acc
      have hacc' : middle.stacks 2 = Encoding.encodeList id acc' := by
        simpa [acc', hacc, Encoding.encodeList] using hout
      obtain ⟨m, next, hm, hnext, hresult, hrest⟩ := ih acc' middle hmiddle hacc'
      have hreader : Eval (RecordPrograms.reader ports) (6 * (clauseCode clause).length + 4)
          (RecordPrograms.afterTag ports base ((clause :: rest).map clauseCode) [])
          (RecordPrograms.state ports base false true false
            (Encoding.encodeList id (rest.map clauseCode)) (clauseCode clause).reverse) := by
        simpa [RecordPrograms.afterTag] using RecordPrograms.reader_eval ports base
          (clauseCode clause) (Encoding.encodeList id (rest.map clauseCode)) [] true true false
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports middle false true false (Encoding.encodeList id (rest.map clauseCode)) [])
          (RecordPrograms.afterTag ports middle (rest.map clauseCode) []) := by
        apply Eval.ite_false (by simp)
        simpa using RecordPrograms.pop_list_eval ports middle (rest.map clauseCode) [] false true
      have hbody := Eval.seq hreader (Eval.seq hc hbranch)
      have hrun := Eval.while_true (body := RecordPrograms.body ports callback)
        (by simp [RecordPrograms.afterTag]) hbody hrest
      refine ⟨(6 * (clauseCode clause).length + 4 + (n + 2)) + m + 1,
        next, ?_, hnext, ?_, hrun⟩
      · simp only [budget]
        omega
      · simpa [ExecCNF.cleanLiterals, acc', List.reverse_cons, List.append_assoc] using hresult

abbrev scan : Cmd 13 11 := RecordPrograms.iterate ports callback

theorem scan_eval (formula : List (List ℕ)) (acc : List (List Bool)) (base : Data)
    (valid : Clean base) (hacc : base.stacks 2 = Encoding.encodeList id acc) (v pr f : Bool) :
    ∃ (n : ℕ) (next : Data), n ≤ 3 + budget formula ∧ Clean next ∧
      next.stacks 2 = Encoding.encodeList id (((ExecCNF.cleanLiterals formula).map clauseCode).reverse ++ acc) ∧
      Eval scan n (RecordPrograms.state ports base v pr f (formulaCode formula) [])
        (RecordPrograms.state ports next false true false [] []) := by
  obtain ⟨n, next, hn, hnext, hout, hloop⟩ := loop_run formula acc base valid hacc
  refine ⟨1 + (1 + n), next, by omega, hnext, hout, ?_⟩
  rw [formulaCode_eq_records]
  apply Eval.seq (RecordPrograms.set_found_eval ports base v pr f false _ [])
  apply Eval.seq _ hloop
  simpa using RecordPrograms.pop_list_eval ports base (formula.map clauseCode) [] v pr

theorem budget_le (formula : List (List ℕ)) : budget formula ≤ 500 * (formulaCode formula).length ^ 2 := by
  induction formula with
  | nil => simp [budget, formulaCode]
  | cons clause rest ih =>
      change budget rest ≤ 500 * (Encoding.encodeList clauseCode rest).length ^ 2 at ih
      simp only [budget, formulaCode, Encoding.length_encodeList_cons]
      nlinarith [Nat.zero_le ((clauseCode clause).length * (clauseCode clause).length),
        Nat.zero_le ((clauseCode clause).length * (Encoding.encodeList clauseCode rest).length)]

theorem cleaned_length_le (formula : List (List ℕ)) :
    (formulaCode (ExecCNF.cleanLiterals formula)).length ≤ (formulaCode formula).length := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      have h := clauseCode_dedup_length_le clause
      change (Encoding.encodeList clauseCode (ExecCNF.cleanLiterals rest)).length ≤
        (Encoding.encodeList clauseCode rest).length at ih
      simp only [formulaCode, ExecCNF.cleanLiterals, List.map_cons, Encoding.length_encodeList_cons]
      change (Encoding.encodeList clauseCode (rest.map ExecCNF.dedupLiterals)).length ≤
        (Encoding.encodeList clauseCode rest).length at ih
      omega

def reverseStack (i : Fin 4) : Fin 11 :=
  if i = 0 then 2 else if i = 1 then 10 else if i = 2 then 0 else 1

theorem reverseStack_injective : Function.Injective reverseStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [reverseStack]

def reverseProgram := ProgramLinking.liftProgram
  SubexpNormalizeProgram.reverseRecordsProgram emitReg reverseStack
abbrev reverseCall : Cmd 13 11 := .call reverseProgram

theorem reverseCall_eval (records acc : List (List Bool)) (d : Data)
    (hsource : d.stacks 2 = Encoding.encodeList id records)
    (houtput : d.stacks 0 = Encoding.encodeList id acc) (hpayload : d.stacks 1 = []) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length, ∃ e : Data,
      Eval reverseCall n d e ∧
      e.stacks 0 = Encoding.encodeList id (records.reverse ++ acc) ∧
      e.stacks 1 = [] ∧ e.stacks 2 = [] ∧
      (∀ i : Fin 8, e.stacks (bankStack i) = d.stacks (bankStack i)) := by
  let a : State 3 4 := ⟨d.regs ∘ emitReg, d.stacks ∘ reverseStack⟩
  have ha : a = SubexpNormalizeProgram.filterState (d.regs 10) (d.regs 11) (d.regs 12)
      (Encoding.encodeList id records) (d.stacks 10) (Encoding.encodeList id acc) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ emitReg ]
    · funext i
      fin_cases i <;> simp [ reverseStack,
        hsource, houtput, hpayload]
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records acc []
    (d.stacks 10) (d.regs 10) (d.regs 11) (d.regs 12)
  simp only [List.append_nil] at ht
  rw [← ha] at ht
  have he := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram
    emitReg reverseStack d emitReg_injective reverseStack_injective ht
  rw [embed_restricted emitReg reverseStack emitReg_injective reverseStack_injective d] at he
  let b := SubexpNormalizeProgram.filterState false true false [] (d.stacks 10)
    (Encoding.encodeList id (records.reverse ++ acc)) []
  let e := embedState emitReg reverseStack d b
  have hs (i : Fin 4) : e.stacks (reverseStack i) = b.stacks i :=
    embedState_stack _ _ _ _ reverseStack_injective i
  refine ⟨n, hn, e, he, ?_, ?_, ?_, ?_⟩
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hs 2
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hs 3
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hs 0
  · intro i
    by_cases hi : i = 7
    · subst i
      simpa [reverseStack, bankStack, b, SubexpNormalizeProgram.filterState] using hs 1
    · apply embedState_stack_frame
      intro h
      rcases h with ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have hi' : i.val ≠ 7 := fun h => hi (Fin.ext h)
      fin_cases j <;> simp [reverseStack, bankStack] at hv <;> omega

abbrev pushFalse (stack : Fin 11) : Cmd 13 11 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push stack 0))

def pushed (stack : Fin 11) (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks stack (false :: d.stacks stack)⟩

theorem pushFalse_eval (stack : Fin 11) (d : Data) : Eval (pushFalse stack) 2 d (pushed stack d) := by
  let middle : Data := ⟨Function.update d.regs 0 false, d.stacks⟩
  have h₁ : Eval (RecordPrograms.atom (.set 0 false)) 1 d middle := by
    apply Eval.base
    simpa [middle, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.set (r := 13) (s := 11) 0 false) d
  have h₂ : Eval (RecordPrograms.atom (.push stack 0)) 1 middle (pushed stack d) := by
    apply Eval.base
    simpa [middle, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 13) (s := 11) stack 0) middle
  exact Eval.seq h₁ h₂

def Ready (d : Data) : Prop := Clean d ∧ d.stacks 1 = [] ∧ d.stacks 2 = []

theorem ready_iff (d : Data) : Ready d ↔ ∀ i : Fin 11, i ≠ 0 → d.stacks i = [] := by
  constructor
  · rintro ⟨hc, h1, h2⟩ i hi
    fin_cases i
    · exact (hi rfl).elim
    · exact h1
    · exact h2
    · exact hc 0
    · exact hc 1
    · exact hc 2
    · exact hc 3
    · exact hc 4
    · exact hc 5
    · exact hc 6
    · exact hc 7
  · intro h
    exact ⟨fun i => h (bankStack i) (bankStack_ne_zero i), h 1 (by decide), h 2 (by decide)⟩

/-- One fixed program maps literal cleanup over every clause and restores
the original clause order. No formula-dependent control table is used. -/
abbrev clean : Cmd 13 11 := .seq (pushFalse 2) (.seq scan (.seq (pushFalse 0) reverseCall))

theorem clean_eval (formula : List (List ℕ)) (d : Data)
    (hsource : d.stacks 0 = formulaCode formula) (hready : Ready d) :
    ∃ n ≤ 500 * (formulaCode formula).length ^ 2 + 10 * (formulaCode formula).length + 7,
      ∃ e : Data, Eval clean n d e ∧ Ready e ∧
        e.stacks 0 = formulaCode (ExecCNF.cleanLiterals formula) := by
  rcases hready with ⟨hclean, hpayload, houtput⟩
  let a := pushed 2 d
  have ha : Clean a := by
    simpa [a, pushed, Clean] using hclean
  have hao : a.stacks 2 = Encoding.encodeList id [] := by
    simp [a, pushed, houtput, Encoding.encodeList]
  obtain ⟨n, next, hn, hnext, hout, hs⟩ := scan_eval formula [] a ha hao
    (a.regs 10) (a.regs 11) (a.regs 12)
  have hstart : RecordPrograms.state ports a (a.regs 10) (a.regs 11) (a.regs 12)
      (formulaCode formula) [] = a := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa [a, pushed, ports] using hsource
    · simpa [a, pushed, ports] using hpayload
  rw [hstart] at hs
  let b := RecordPrograms.state ports next false true false [] []
  let c := pushed 0 b
  have hc : Clean c := by
    simpa [c, pushed, b, Clean, RecordPrograms.state, ports] using hnext
  have hc2 : c.stacks 2 =
      Encoding.encodeList id ((ExecCNF.cleanLiterals formula).map clauseCode).reverse := by
    simpa [c, pushed, b] using hout
  have hc0 : c.stacks 0 = Encoding.encodeList id [] := by
    simp [c, pushed, b, RecordPrograms.state, ports, Encoding.encodeList]
  have hc1 : c.stacks 1 = [] := by
    simp [c, pushed, b, RecordPrograms.state, ports]
  obtain ⟨m, hm, e, he, he0, he1, he2, hew⟩ :=
    reverseCall_eval ((ExecCNF.cleanLiterals formula).map clauseCode).reverse [] c hc2 hc0 hc1
  have hcost := budget_le formula
  have hlength := cleaned_length_le formula
  rw [ExecLiteralDedupProgram.encoded_reverse_length, ← formulaCode_eq_records] at hm
  refine ⟨2 + (n + (2 + m)), ?_, e, ?_, ?_, ?_⟩
  · omega
  · exact Eval.seq (pushFalse_eval 2 d) (Eval.seq hs (Eval.seq (pushFalse_eval 0 b) he))
  · exact ⟨fun i => (hew i).trans (hc i), he1, he2⟩
  · simpa only [List.reverse_reverse, List.append_nil, ← formulaCode_eq_records] using he0

def cleanProgram := compiled clean 0 0

theorem clean_runsIn (formula : List (List ℕ)) (d : Data)
    (hsource : d.stacks 0 = formulaCode formula) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 0 = formulaCode (ExecCNF.cleanLiterals formula) ∧
      RunsIn cleanProgram (600 * ((formulaCode formula).length + 1) ^ 2)
        (d.withPC (some cleanProgram.entry)) (e.withPC none) := by
  obtain ⟨n, hn, e, he, hready', hout⟩ := clean_eval formula d hsource hready
  refine ⟨e, hready', hout, n + 1, ?_, compiled_halt_trace he 0 0⟩
  nlinarith

theorem clean_primitive_execution (formula : List (List ℕ)) (d : Data)
    (hsource : d.stacks 0 = formulaCode formula) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 0 = formulaCode (ExecCNF.cleanLiterals formula) ∧
      Computation.RunsIn (primitive cleanProgram).step
        (primitiveOverhead cleanProgram * (600 * ((formulaCode formula).length + 1) ^ 2))
        (primitiveCfg cleanProgram (d.withPC (some cleanProgram.entry)))
        (primitiveCfg cleanProgram (e.withPC none)) := by
  obtain ⟨e, he, hout, hrun⟩ := clean_runsIn formula d hsource hready
  exact ⟨e, he, hout, primitive_execution cleanProgram hrun⟩

end SubexponentialSAT.ExecCleanLiteralsProgram

end OAI.Algorithms

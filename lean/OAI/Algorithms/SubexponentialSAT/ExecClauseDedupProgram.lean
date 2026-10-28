import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram
import OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScanEncoding
import OAI.Algorithms.SubexponentialSAT.ExecLiteralDedupProgram
import OAI.Algorithms.SubexponentialSAT.ExecClauseFilterReverse
import OAI.Algorithms.SubexponentialSAT.ExecCNFCodeTransport

namespace OAI.Algorithms

/-!
# A fixed program for last-occurrence clause deduplication

The current clause is compared with the unread suffix using actual set
equivalence of its literal records. The suffix copy is cleared after each
query, and the final record reversal restores the prescribed clause order.
-/

namespace SubexponentialSAT.ExecClauseDedupProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram (Regs Data state reset flags)

def workPort (i : Fin 13) : Fin 16 := Fin.castAdd 3 i

@[simp] theorem workPort_ne_source (i : Fin 13) : workPort i ≠ 13 := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = 13 at hv
  omega

@[simp] theorem workPort_ne_output (i : Fin 13) : workPort i ≠ 14 := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = 14 at hv
  omega

@[simp] theorem workPort_ne_payload (i : Fin 13) : workPort i ≠ 15 := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = 15 at hv
  omega

def Clean (d : Data) : Prop := ∀ i : Fin 13, d.stacks (workPort i) = []

theorem clean_canonical (regs : Regs) (source output payload : List Bool) :
    Clean (state regs [] [] [] source output payload) := by
  intro i
  fin_cases i <;> rfl

theorem eq_canonical (d : Data) (hc : Clean d) :
    d = state d.regs [] [] [] (d.stacks 13) (d.stacks 14) (d.stacks 15) := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> first
    | exact hc 0
    | exact hc 1
    | exact hc 2
    | exact hc 3
    | exact hc 4
    | exact hc 5
    | exact hc 6
    | exact hc 7
    | exact hc 8
    | exact hc 9
    | exact hc 10
    | exact hc 11
    | exact hc 12
    | rfl

abbrev copySuffix : Cmd 15 16 := .call (StackRoutines.copyProgram 13 12 9 0 1)

theorem copySuffix_eval (regs : Regs) (source output payload : List Bool) :
    Eval copySuffix (7 * source.length + 5)
      (state regs [] [] [] source output payload)
      (state (reset regs) [] [] source source output payload) := by
  have h := ListRegisterProgram.copy_run (r := 15) (s := 16)
    13 12 9 0 1 (by decide) (by decide) (by decide) (by decide)
    regs (state regs [] [] [] source output payload).stacks (by rfl)
  have hs : StackRoutines.copyStacks 13 12
      (state regs [] [] [] source output payload).stacks =
      (state (reset regs) [] [] source source output payload).stacks := by
    funext i
    fin_cases i <;> simp [StackRoutines.copyStacks, state]
  rw [hs] at h
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, state, reset] using h

theorem clearMaster_eval (regs : Regs) (master source output payload : List Bool) :
    Eval (ExecClauseFiltersProgram.clear 12) (2 * master.length + 3)
      (state regs [] [] master source output payload)
      (state (reset regs) [] [] [] source output payload) := by
  have heq : ExecClauseFiltersProgram.cleared 12 (state regs [] [] master source output payload) =
      state (reset regs) [] [] [] source output payload := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [ state, StackRoutines.clearStacks]
  have h := ExecClauseFiltersProgram.clear_eval 12
    (state regs [] [] master source output payload)
  rw [heq] at h
  simpa [state] using h

abbrev callback : Cmd 15 16 := .seq copySuffix
  (.seq (ExecClauseFiltersProgram.callback .equivalent) (ExecClauseFiltersProgram.clear 12))

def callbackBound (rest : Formula) (clause : Clause) : ℕ :=
  ExecClauseFiltersProgram.callbackBound rest clause + 9 * (encodeFormula rest).length + 8

theorem equivalent_comm {α : Type*} [DecidableEq α] (C D : List α) :
    ExecCNF.equivalent C D = ExecCNF.equivalent D C := by
  exact Bool.and_comm _ _

theorem any_equivalent (rest : Formula) (clause : Clause) :
    rest.any (fun C => ExecClauseRelationScan.test .equivalent C clause) =
      rest.any (fun C => ExecCNF.equivalent clause C) := by
  congr 1
  funext C
  exact equivalent_comm C clause

theorem callback_canonical (rest : Formula) (clause : Clause) (regs : Regs)
    (output : List Bool) :
    ∃ (n : ℕ) (rf : Regs), n ≤ callbackBound rest clause ∧
      rf 0 = false ∧ rf 1 = false ∧ rf 14 = false ∧
      Eval callback n
        (state regs [] [] [] (encodeFormula rest) output (encodeClause clause).reverse)
        (state rf [] [] [] (encodeFormula rest)
          (if rest.any (fun C => ExecCNF.equivalent clause C) then output
            else true :: (Encoding.frame (encodeClause clause) ++ output)) []) := by
  obtain ⟨n, rf, hn, h0, h1, h14, he⟩ :=
    ExecClauseFiltersProgram.callback_eval .equivalent rest clause (reset regs)
      (encodeFormula rest) output
  rw [any_equivalent] at he
  have hout : (if !(rest.any (fun C => ExecCNF.equivalent clause C)) then
      true :: (Encoding.frame (encodeClause clause) ++ output) else output) =
      (if rest.any (fun C => ExecCNF.equivalent clause C) then output
        else true :: (Encoding.frame (encodeClause clause) ++ output)) := by
    cases rest.any (fun C => ExecCNF.equivalent clause C) <;> rfl
  rw [hout] at he
  refine ⟨(7 * (encodeFormula rest).length + 5) + (n + (2 * (encodeFormula rest).length + 3)),
    reset rf, ?_, ?_, ?_, ?_, ?_⟩
  · unfold callbackBound
    omega
  · simp [reset, readRegs]
  · simp [reset, readRegs]
  · simpa [reset, readRegs] using h14
  · exact Eval.seq (copySuffix_eval regs _ _ _) (Eval.seq he (clearMaster_eval rf _ _ _ _))

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

@[simp] theorem clean_state (base : Data) (v pr f : Bool) (src payload : List Bool) :
    Clean (RecordPrograms.state ports base v pr f src payload) ↔ Clean base := by
  simp [Clean, RecordPrograms.state, ports]

@[simp] theorem state_output (base : Data) (v pr f : Bool) (src payload : List Bool) :
    (RecordPrograms.state ports base v pr f src payload).stacks 14 = base.stacks 14 := by
  simp [RecordPrograms.state, ports]

theorem callback_state_eval (rest : Formula) (clause : Clause) (base : Data)
    (hc : Clean base) :
    ∃ (n : ℕ) (next : Data), n ≤ callbackBound rest clause ∧ Clean next ∧
      next.stacks 14 = (if rest.any (fun C => ExecCNF.equivalent clause C) then base.stacks 14
        else true :: (Encoding.frame (encodeClause clause) ++ base.stacks 14)) ∧
      Eval callback n
        (RecordPrograms.state ports base false true false (encodeFormula rest) (encodeClause clause).reverse)
        (RecordPrograms.state ports next false false false (encodeFormula rest) []) := by
  let d := RecordPrograms.state ports base false true false (encodeFormula rest) (encodeClause clause).reverse
  have hd : Clean d := (clean_state _ _ _ _ _ _).mpr hc
  have hrepr : d = state d.regs [] [] [] (encodeFormula rest) (base.stacks 14)
      (encodeClause clause).reverse := by
    simpa [d, RecordPrograms.state, ports] using eq_canonical d hd
  obtain ⟨n, rf, hn, h0, h1, h14, he⟩ := callback_canonical rest clause d.regs (base.stacks 14)
  rw [← hrepr] at he
  let next := state rf [] [] [] (encodeFormula rest)
    (if rest.any (fun C => ExecCNF.equivalent clause C) then base.stacks 14
      else true :: (Encoding.frame (encodeClause clause) ++ base.stacks 14)) []
  have hend : RecordPrograms.state ports next false false false (encodeFormula rest) [] = next :=
    RecordPrograms.state_eq_self ports next false false false _ [] h0 h1 h14 rfl rfl
  refine ⟨n, next, hn, clean_canonical _ _ _ _, rfl, ?_⟩
  rw [hend]
  exact he

def budget : Formula → ℕ
  | [] => 0
  | clause :: rest => 6 * (encodeClause clause).length + callbackBound rest clause + 7 + budget rest

theorem encodeFormula_records (formula : Formula) :
    encodeFormula formula = Encoding.encodeList id (formula.map encodeClause) := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      exact congrArg (fun tail => true :: (Encoding.frame (encodeClause clause) ++ tail)) ih

theorem loop_run (formula : Formula) (acc : List (List Bool)) (base : Data)
    (hc : Clean base) (hacc : base.stacks 14 = Encoding.encodeList id acc) :
    ∃ (n : ℕ) (next : Data), n ≤ 1 + budget formula ∧ Clean next ∧
      next.stacks 14 = Encoding.encodeList id (((ExecCNF.dedupClauses formula).map encodeClause).reverse ++ acc) ∧
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports base (formula.map encodeClause) [])
        (RecordPrograms.state ports next false true false [] []) := by
  induction formula generalizing base acc with
  | nil =>
      refine ⟨1, base, by simp [budget], hc, ?_, ?_⟩
      · simpa [ExecCNF.dedupClauses] using hacc
      · apply Eval.while_false
        simp [RecordPrograms.afterTag]
  | cons clause rest ih =>
      obtain ⟨n, middle, hn, hmiddle, hout, he⟩ := callback_state_eval rest clause base hc
      let acc' := if rest.any (fun C => ExecCNF.equivalent clause C) then acc else encodeClause clause :: acc
      have hacc' : middle.stacks 14 = Encoding.encodeList id acc' := by
        cases h : rest.any (fun C => ExecCNF.equivalent clause C) <;>
          simpa [acc', h, hacc, Encoding.encodeList] using hout
      obtain ⟨m, next, hm, hnext, hresult, hrest⟩ := ih acc' middle hmiddle hacc'
      have hreader : Eval (RecordPrograms.reader ports) (6 * (encodeClause clause).length + 4)
          (RecordPrograms.afterTag ports base ((clause :: rest).map encodeClause) [])
          (RecordPrograms.state ports base false true false (encodeFormula rest) (encodeClause clause).reverse) := by
        simpa [RecordPrograms.afterTag, ← encodeFormula_records] using RecordPrograms.reader_eval ports base
          (encodeClause clause) (Encoding.encodeList id (rest.map encodeClause)) [] true true false
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports middle false false false (encodeFormula rest) [])
          (RecordPrograms.afterTag ports middle (rest.map encodeClause) []) := by
        apply Eval.ite_false (by simp)
        simpa [← encodeFormula_records] using RecordPrograms.pop_list_eval ports middle
          (rest.map encodeClause) [] false false
      have hbody := Eval.seq hreader (Eval.seq he hbranch)
      have hrun := Eval.while_true (body := RecordPrograms.body ports callback)
        (by simp [RecordPrograms.afterTag]) hbody hrest
      refine ⟨(6 * (encodeClause clause).length + 4 + (n + 2)) + m + 1,
        next, ?_, hnext, ?_, hrun⟩
      · simp only [budget]
        omega
      · cases h : rest.any (fun C => ExecCNF.equivalent clause C) <;>
          simpa [ExecCNF.dedupClauses, h, acc', List.reverse_cons, List.append_assoc] using hresult

abbrev scan : Cmd 15 16 := RecordPrograms.iterate ports callback

theorem scan_eval (formula : Formula) (acc : List (List Bool)) (base : Data)
    (hc : Clean base) (hacc : base.stacks 14 = Encoding.encodeList id acc) (v pr f : Bool) :
    ∃ (n : ℕ) (next : Data), n ≤ 3 + budget formula ∧ Clean next ∧
      next.stacks 14 = Encoding.encodeList id (((ExecCNF.dedupClauses formula).map encodeClause).reverse ++ acc) ∧
      Eval scan n (RecordPrograms.state ports base v pr f (encodeFormula formula) [])
        (RecordPrograms.state ports next false true false [] []) := by
  obtain ⟨n, next, hn, hnext, hout, hloop⟩ := loop_run formula acc base hc hacc
  refine ⟨1 + (1 + n), next, by omega, hnext, hout, ?_⟩
  rw [encodeFormula_records]
  apply Eval.seq (RecordPrograms.set_found_eval ports base v pr f false _ [])
  apply Eval.seq _ hloop
  simpa using RecordPrograms.pop_list_eval ports base (formula.map encodeClause) [] v pr

theorem budget_le (formula : Formula) : budget formula ≤ 1000 * (encodeFormula formula).length ^ 2 := by
  induction formula with
  | nil => simp [budget, encodeFormula]
  | cons clause rest ih =>
      change budget rest ≤ 1000 * (Encoding.encodeList encodeClause rest).length ^ 2 at ih
      simp only [budget, callbackBound, ExecClauseFiltersProgram.callbackBound,
        ExecClauseRelationScan.Preserving.bound, encodeFormula, Encoding.length_encodeList_cons]
      nlinarith [Nat.zero_le ((encodeClause clause).length * (encodeClause clause).length),
        Nat.zero_le ((encodeClause clause).length * (Encoding.encodeList encodeClause rest).length)]

theorem encoded_dedup_length_le (formula : Formula) :
    (encodeFormula (ExecCNF.dedupClauses formula)).length ≤ (encodeFormula formula).length := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      unfold ExecCNF.dedupClauses
      split
      · simp only [encodeFormula, Encoding.length_encodeList_cons]
        exact ih.trans (by simp [encodeFormula])
      · simpa only [encodeFormula, Encoding.length_encodeList_cons] using
          Nat.add_le_add_left ih (2 * (encodeClause clause).length + 2)

abbrev reverseCall : Cmd 15 16 := ExecClauseFilterReverse.command

theorem reverseCall_eval (records acc : List (List Bool)) (d : Data) (hc : Clean d)
    (hs : d.stacks 14 = Encoding.encodeList id records)
    (ho : d.stacks 13 = Encoding.encodeList id acc) (hp : d.stacks 15 = []) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length, ∃ e : Data,
      Eval reverseCall n d e ∧ Clean e ∧
      e.stacks 13 = Encoding.encodeList id (records.reverse ++ acc) ∧
      e.stacks 14 = [] ∧ e.stacks 15 = [] := by
  have hd : d = ExecClauseFilterReverse.state d.regs
      (Encoding.encodeList id acc) (Encoding.encodeList id records) [] := by
    simpa only [hs, ho, hp, ExecClauseFiltersProgram.state,
      ExecClauseFilterReverse.state] using eq_canonical d hc
  obtain ⟨n, hn, he⟩ := ExecClauseFilterReverse.reverse_eval records acc d.regs
  rw [← hd] at he
  refine ⟨n, hn, _, he, ?_, rfl, rfl, rfl⟩
  exact clean_canonical _ _ _ _

abbrev pushFalse (stack : Fin 16) : Cmd 15 16 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push stack 0))

def pushed (stack : Fin 16) (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks stack (false :: d.stacks stack)⟩

theorem pushFalse_eval (stack : Fin 16) (d : Data) : Eval (pushFalse stack) 2 d (pushed stack d) := by
  let middle : Data := ⟨Function.update d.regs 0 false, d.stacks⟩
  have h₁ : Eval (RecordPrograms.atom (.set 0 false)) 1 d middle := by
    apply Eval.base
    simpa [middle, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.set (r := 15) (s := 16) 0 false) d
  have h₂ : Eval (RecordPrograms.atom (.push stack 0)) 1 middle (pushed stack d) := by
    apply Eval.base
    simpa [middle, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 15) (s := 16) stack 0) middle
  exact Eval.seq h₁ h₂

def Ready (d : Data) : Prop := ∀ i : Fin 16, i ≠ 13 → d.stacks i = []

theorem ready_iff (d : Data) : Ready d ↔ Clean d ∧ d.stacks 14 = [] ∧ d.stacks 15 = [] := by
  constructor
  · intro h
    exact ⟨fun i => h (workPort i) (workPort_ne_source i), h 14 (by decide), h 15 (by decide)⟩
  · rintro ⟨hc, h14, h15⟩ i hi
    fin_cases i <;> first
      | exact hc 0
      | exact hc 1
      | exact hc 2
      | exact hc 3
      | exact hc 4
      | exact hc 5
      | exact hc 6
      | exact hc 7
      | exact hc 8
      | exact hc 9
      | exact hc 10
      | exact hc 11
      | exact hc 12
      | exact (hi rfl).elim
      | exact h14
      | exact h15

/-- Both sentinels and the final outer reversal are actual instructions. -/
abbrev command : Cmd 15 16 := .seq (pushFalse 14) (.seq scan (.seq (pushFalse 13) reverseCall))

theorem command_eval (formula : Formula) (d : Data)
    (hsource : d.stacks 13 = encodeFormula formula) (hready : Ready d) :
    ∃ n ≤ 1000 * (encodeFormula formula).length ^ 2 + 10 * (encodeFormula formula).length + 7,
      ∃ e : Data, Eval command n d e ∧ Ready e ∧
        e.stacks 13 = encodeFormula (ExecCNF.dedupClauses formula) := by
  rcases (ready_iff d).mp hready with ⟨hclean, houtput, hpayload⟩
  let a := pushed 14 d
  have ha : Clean a := by
    simpa [a, pushed, Clean] using hclean
  have hao : a.stacks 14 = Encoding.encodeList id [] := by
    simp [a, pushed, houtput, Encoding.encodeList]
  obtain ⟨n, next, hn, hnext, hout, hs⟩ := scan_eval formula [] a ha hao
    (a.regs 0) (a.regs 1) (a.regs 14)
  have hstart : RecordPrograms.state ports a (a.regs 0) (a.regs 1) (a.regs 14)
      (encodeFormula formula) [] = a := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa [a, pushed, ports] using hsource
    · simpa [a, pushed, ports] using hpayload
  rw [hstart] at hs
  let b := RecordPrograms.state ports next false true false [] []
  let c := pushed 13 b
  have hc : Clean c := by
    simpa [c, pushed, b, Clean, RecordPrograms.state, ports] using hnext
  have hc14 : c.stacks 14 =
      Encoding.encodeList id ((ExecCNF.dedupClauses formula).map encodeClause).reverse := by
    simpa [c, pushed, b] using hout
  have hc13 : c.stacks 13 = Encoding.encodeList id [] := by
    simp [c, pushed, b, RecordPrograms.state, ports, Encoding.encodeList]
  have hc15 : c.stacks 15 = [] := by
    simp [c, pushed, b, RecordPrograms.state, ports]
  obtain ⟨m, hm, e, he, hce, he13, he14, he15⟩ :=
    reverseCall_eval ((ExecCNF.dedupClauses formula).map encodeClause).reverse [] c hc hc14 hc13 hc15
  have hcost := budget_le formula
  have hlength := encoded_dedup_length_le formula
  rw [ExecLiteralDedupProgram.encoded_reverse_length, ← encodeFormula_records] at hm
  refine ⟨2 + (n + (2 + m)), ?_, e, ?_, (ready_iff e).mpr ⟨hce, he14, he15⟩, ?_⟩
  · omega
  · exact Eval.seq (pushFalse_eval 14 d) (Eval.seq hs (Eval.seq (pushFalse_eval 13 b) he))
  · simpa only [List.reverse_reverse, List.append_nil, ← encodeFormula_records] using he13

def program := compiled command 13 13

theorem generic_runsIn (formula : Formula) (d : Data)
    (hsource : d.stacks 13 = encodeFormula formula) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 13 = encodeFormula (ExecCNF.dedupClauses formula) ∧
      RunsIn program (1200 * ((encodeFormula formula).length + 1) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨n, hn, e, he, hready', hout⟩ := command_eval formula d hsource hready
  refine ⟨e, hready', hout, n + 1, ?_, compiled_halt_trace he 13 13⟩
  nlinarith

def formulaCode (formula : List (List ℕ)) : List Bool :=
  Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) formula

theorem dedup_codes (formula : List (List ℕ)) :
    ExecCNF.dedupClauses (ExecClauseRelationScan.codeFormula formula) =
      ExecClauseRelationScan.codeFormula (ExecCNF.dedupClauses formula) :=
  ExecCNFCodeTransport.dedupClauses_map Encoding.encodeNat Encoding.encodeNat_injective formula

theorem formulaCode_dedup_length_le (formula : List (List ℕ)) :
    (formulaCode (ExecCNF.dedupClauses formula)).length ≤ (formulaCode formula).length := by
  have h := encoded_dedup_length_le (ExecClauseRelationScan.codeFormula formula)
  rw [dedup_codes, ExecClauseRelationScan.encodeFormula_codes,
    ExecClauseRelationScan.encodeFormula_codes] at h
  exact h

/-- The fixed program implements precisely the executable normalizer's
last-occurrence clause deduplication, including differently ordered clauses. -/
theorem program_runsIn (formula : List (List ℕ)) (d : Data)
    (hsource : d.stacks 13 = formulaCode formula) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 13 = formulaCode (ExecCNF.dedupClauses formula) ∧
      RunsIn program (1200 * ((formulaCode formula).length + 1) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  have hs : d.stacks 13 = encodeFormula (ExecClauseRelationScan.codeFormula formula) := by
    simpa only [formulaCode, ExecClauseRelationScan.encodeFormula_codes] using hsource
  obtain ⟨e, he, hout, hr⟩ := generic_runsIn (ExecClauseRelationScan.codeFormula formula) d hs hready
  rw [dedup_codes, ExecClauseRelationScan.encodeFormula_codes] at hout
  exact ⟨e, he, hout, by
    simpa only [formulaCode, ExecClauseRelationScan.encodeFormula_codes] using hr⟩

theorem primitive_execution (formula : List (List ℕ)) (d : Data)
    (hsource : d.stacks 13 = formulaCode formula) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 13 = formulaCode (ExecCNF.dedupClauses formula) ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (1200 * ((formulaCode formula).length + 1) ^ 2))
        (primitiveCfg program (d.withPC (some program.entry)))
        (primitiveCfg program (e.withPC none)) := by
  obtain ⟨e, he, hout, hr⟩ := program_runsIn formula d hsource hready
  exact ⟨e, he, hout, BitProgram.primitive_execution program hr⟩

end SubexponentialSAT.ExecClauseDedupProgram

end OAI.Algorithms

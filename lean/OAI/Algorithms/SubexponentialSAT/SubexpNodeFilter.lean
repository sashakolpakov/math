import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeFilterSpec
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-!
# A fixed-control nonzero-record filter for field nodes

The parser supplies each reversed payload. The callback copies it, executes
the verified positivity scanner on the copy, and emits the preserved original
exactly when it is nonzero. Retained records are prepended, so their final order
is the reverse of the input's filtered order.
-/

namespace SubexponentialSAT.SubexpNodeFilter

open BitProgram StructuredCalls Subexp.TupleProgram

/-- Parser registers 0,1,2; scan registers 3,4; register 5 is framed.
Stacks: unread records 0, original payload 1, scan copy 2, copy scratch 3,
retained output records 4. -/
def ports : RecordPrograms.Ports 6 5 :=
  ⟨0, 1, 2, 0, 1, by decide, by decide, by decide, by decide⟩

def emitPorts : RecordPrograms.Ports 6 5 :=
  ⟨3, 4, 5, 1, 4, by decide, by decide, by decide, by decide⟩

def scanRegister : Fin 2 → Fin 6 := ![3, 4]
def scanPort : Fin 1 → Fin 5 := fun _ => 2

theorem scanRegister_injective : Function.Injective scanRegister := by decide
theorem scanPort_injective : Function.Injective scanPort := by decide

abbrev scanProgram : Program 6 5 7 :=
  ProgramLinking.liftProgram PositiveWordProgram.program scanRegister scanPort

abbrev scanRegs (regs : Fin 6 → Bool) (v pr : Bool) : Fin 6 → Bool :=
  Function.update (Function.update regs 3 v) 4 pr

private theorem embed_scan (pc : Option (Fin 7)) (a : State 6 5)
    (v pr : Bool) (word : List Bool) :
    ProgramLinking.embedCfg scanRegister scanPort id none
      (a.withPC none) (PositiveWordProgram.cfg pc v pr word) =
      ⟨pc, scanRegs a.regs v pr, Function.update a.stacks 2 word⟩ := by
  apply ProgramLinking.embedCfg_eq_of_ports scanRegister scanPort id none _ _ _
    scanRegister_injective scanPort_injective
  · cases pc <;> rfl
  · intro i
    fin_cases i <;> simp [scanRegister, scanRegs, PositiveWordProgram.cfg,
      PositiveWordProgram.regs]
  · intro i hi
    have h3 : i ≠ 3 := fun he => hi ⟨0, by simpa [scanRegister] using he.symm⟩
    have h4 : i ≠ 4 := fun he => hi ⟨1, by simpa [scanRegister] using he.symm⟩
    simp [scanRegs, h3, h4 ]
  · intro i
    fin_cases i
    simp [scanPort, PositiveWordProgram.cfg]
  · intro i hi
    have h2 : i ≠ 2 := fun he => hi ⟨0, by simpa [scanPort] using he.symm⟩
    simp [h2 ]

abbrev scannedState (a : State 6 5) : State 6 5 :=
  let yes := PositiveWordProgram.positive (a.stacks 2)
  ⟨scanRegs a.regs yes yes, Function.update a.stacks 2
    (yes :: PositiveWordProgram.residual (a.stacks 2))⟩

theorem scan_eval (a : State 6 5) :
    Eval (.call scanProgram) (PositiveWordProgram.cost (a.stacks 2)) a (scannedState a) := by
  apply Eval.call
  have h := ProgramLinking.liftProgram_trace PositiveWordProgram.program scanRegister scanPort
    (a.withPC none) scanRegister_injective scanPort_injective
    (PositiveWordProgram.run (a.stacks 2) (a.regs 3) (a.regs 4))
  rw [embed_scan (some 0) a (a.regs 3) (a.regs 4) (a.stacks 2),
    embed_scan none a (PositiveWordProgram.positive (a.stacks 2))
      (PositiveWordProgram.positive (a.stacks 2))
      (PositiveWordProgram.positive (a.stacks 2) ::
        PositiveWordProgram.residual (a.stacks 2))] at h
  simpa only [scanRegs, Function.update_eq_self, scannedState,
    StructuredProgram.State.withPC] using h

abbrev emit : Cmd 6 5 :=
  .seq (pushConst 4 3 false) (.seq (escape emitPorts) (pushConst 4 3 true))

abbrev emittedState (a : State 6 5) : State 6 5 :=
  pushedState 4 3 true (escapedState emitPorts (pushedState 4 3 false a))

theorem emit_eval (a : State 6 5) :
    Eval emit (5 * (a.stacks 1).length + 7) a (emittedState a) := by
  have h := (pushConst_eval 4 3 false a).seq
    ((escape_eval_state emitPorts (pushedState 4 3 false a)).seq
      (pushConst_eval 4 3 true (escapedState emitPorts (pushedState 4 3 false a))))
  convert h using 1 ; simp [ emitPorts ] ; omega

abbrev copiedState (a : State 6 5) : State 6 5 :=
  ⟨readRegs a.regs 3 4 none, StackRoutines.copyStacks 1 2 a.stacks⟩

abbrev clearedState (src : Fin 5) (a : State 6 5) : State 6 5 :=
  ⟨readRegs a.regs 3 4 none, StackRoutines.clearStacks src a.stacks⟩

abbrev callback : Cmd 6 5 :=
  .seq (.call (StackRoutines.copyProgram 1 2 3 3 4))
    (.seq (.call scanProgram)
      (.seq (.ite 3 emit (.call (StackRoutines.clearProgram 1 3 4)))
        (.call (StackRoutines.clearProgram 2 3 4))))

def invariant (a : State 6 5) : Prop := a.stacks 2 = [] ∧ a.stacks 3 = []

def retain (bits out : List Bool) : List Bool :=
  if PositiveWordProgram.positive bits then prependRecord bits out else out

theorem residual_length_le (bits : List Bool) :
    (PositiveWordProgram.residual bits).length ≤ bits.length := by
  induction bits with
  | nil => simp [PositiveWordProgram.residual]
  | cons b bits ih =>
      cases b <;> simp [PositiveWordProgram.residual] ; omega

theorem callback_contract :
    RecordPrograms.CallbackContractWith ports callback (fun _ => false)
      (fun bits => 20 * bits.length + 40) invariant
      (fun bits a b => b.stacks 4 = retain bits (a.stacks 4)) := by
  intro bits tail base hb
  let a := RecordPrograms.state ports base false true false tail bits.reverse
  let b := copiedState a
  let c := scannedState b
  have hcopy : a.stacks 3 = [] := by simpa [a, ports, RecordPrograms.state] using hb.2
  have ha1 : a.stacks 1 = bits.reverse := by simp [a, ports, RecordPrograms.state]
  have h1 := copy_eval 1 2 3 3 4 (by decide) (by decide) (by decide) (by decide) a hcopy
  have h2 := scan_eval b
  have hb2 : b.stacks 2 = bits.reverse := by
    simp [b, a, ports, RecordPrograms.state, StackRoutines.copyStacks,
      hb.1]
  have hc1 : c.stacks 1 = bits.reverse := by
    simp [c, b, a, ports, RecordPrograms.state,
      StackRoutines.copyStacks]
  have hc2 : c.stacks 2 = PositiveWordProgram.positive bits ::
      PositiveWordProgram.residual bits.reverse := by
    simp [c, hb2, SubexpNodeFilterSpec.positive_reverse]
  have hc3 : c.regs 3 = PositiveWordProgram.positive bits := by
    simp [c, scanRegs, hb2, SubexpNodeFilterSpec.positive_reverse]
  have hscan := PositiveWordProgram.cost_le bits.reverse
  have hres := residual_length_le bits.reverse
  cases hp : PositiveWordProgram.positive bits with
  | false =>
      let d := clearedState 1 c
      let e := clearedState 2 d
      have h3 := clear_eval 1 3 4 c
      have h4 := clear_eval 2 3 4 d
      have hi : Eval (.ite 3 emit (.call (StackRoutines.clearProgram 1 3 4)))
          (2 * (c.stacks 1).length + 3 + 1) c d :=
        Eval.ite_false (hc3.trans hp) h3
      have hr := h1.seq (h2.seq (hi.seq h4))
      have hd2 : d.stacks 2 = c.stacks 2 := by simp [d, StackRoutines.clearStacks]
      refine ⟨(7 * (a.stacks 1).length + 5) +
        (PositiveWordProgram.cost (b.stacks 2) +
          ((2 * (c.stacks 1).length + 3 + 1) + (2 * (d.stacks 2).length + 3))),
        e, ?_, ?_, ?_, ?_⟩
      · simp only [ha1, hb2, hc1, hd2, hc2, List.length_cons, List.length_reverse]
        simp only [List.length_reverse] at hscan hres
        omega
      · simp [invariant, e, d, c, b, a,
          StackRoutines.clearStacks, StackRoutines.copyStacks, ports,
          RecordPrograms.state, hb.2]
      · simp [retain, hp, e, d, c, b, a,
          StackRoutines.clearStacks, StackRoutines.copyStacks, ports, RecordPrograms.state]
      · have he : RecordPrograms.state ports e false true false tail [] = e := by
          apply RecordPrograms.state_eq_self <;>
            simp [e, d, c, b, a, scanRegs,
              StackRoutines.clearStacks, StackRoutines.copyStacks, ports,
              RecordPrograms.state, readRegs]
        rw [he]
        exact hr
  | true =>
      let d := emittedState c
      let e := clearedState 2 d
      have h3 := emit_eval c
      have h4 := clear_eval 2 3 4 d
      have hi : Eval (.ite 3 emit (.call (StackRoutines.clearProgram 1 3 4)))
          (5 * (c.stacks 1).length + 7 + 1) c d :=
        Eval.ite_true (hc3.trans hp) h3
      have hr := h1.seq (h2.seq (hi.seq h4))
      have hd2 : d.stacks 2 = c.stacks 2 := by
        simp [d, emitPorts]
      refine ⟨(7 * (a.stacks 1).length + 5) +
        (PositiveWordProgram.cost (b.stacks 2) +
          ((5 * (c.stacks 1).length + 7 + 1) + (2 * (d.stacks 2).length + 3))),
        e, ?_, ?_, ?_, ?_⟩
      · simp only [ha1, hb2, hc1, hd2, hc2, List.length_cons, List.length_reverse]
        simp only [List.length_reverse] at hscan hres
        omega
      · simp [invariant, e, d, c, b, a, emitPorts, StackRoutines.clearStacks,
          StackRoutines.copyStacks, ports, RecordPrograms.state, hb.2]
      · simp [retain, hp, e, d, c, b, a, emitPorts, StackRoutines.clearStacks,
          StackRoutines.copyStacks, ports, RecordPrograms.state, prependRecord,
          frame_eq_escaped, List.append_assoc]
      · have he : RecordPrograms.state ports e false true false tail [] = e := by
          apply RecordPrograms.state_eq_self <;>
            simp [e, d, c, b, a,
              emitPorts, scanRegs, StackRoutines.clearStacks,
              StackRoutines.copyStacks, ports, RecordPrograms.state, readRegs]
        rw [he]
        exact hr

theorem fold_retain (words : List (List Bool)) (out : List Bool) :
    words.foldl (fun out bits => retain bits out) out =
      appendEncoded ((words.filter PositiveWordProgram.positive).reverse) out := by
  rw [← fold_prependRecord]
  induction words generalizing out with
  | nil => rfl
  | cons bits words ih =>
      cases hp : PositiveWordProgram.positive bits <;>
        simp [retain, hp ] <;> exact ih _

abbrev cmd : Cmd 6 5 := RecordPrograms.iterate ports callback

def budget (words : List (List Bool)) : ℕ :=
  3 + RecordPrograms.budget (fun bits => 20 * bits.length + 40) words

/-- Complete measured execution of the fixed filter command, including
preservation of previously accumulated output records. -/
theorem cmd_eval (words accum : List (List Bool)) (base : State 6 5)
    (hb : invariant base) (hin : base.stacks 0 = ProgramEncoding.encodeRecords words)
    (hpayload : base.stacks 1 = [])
    (hout : base.stacks 4 = ProgramEncoding.encodeRecords accum) :
    ∃ n next, n ≤ budget words ∧ invariant next ∧ next.stacks 0 = [] ∧
      next.stacks 1 = [] ∧
      next.stacks 4 = ProgramEncoding.encodeRecords
        ((words.filter PositiveWordProgram.positive).reverse ++ accum) ∧
      Eval cmd n base next := by
  obtain ⟨n, next, hn, hnext, history, hiter⟩ :=
    RecordPrograms.iterate_run_with ports callback (fun _ => false)
      (fun bits => 20 * bits.length + 40) invariant
      (fun bits a b => b.stacks 4 = retain bits (a.stacks 4))
      callback_contract words [] base hb (base.regs 0) (base.regs 1) (base.regs 2)
  let final := RecordPrograms.state ports next false true false [] []
  have hstart : RecordPrograms.state ports base (base.regs 0) (base.regs 1)
      (base.regs 2) (Encoding.encodeList id words ++ []) [] = base := by
    apply RecordPrograms.state_eq_self <;>
      simp_all [ports, ProgramEncoding.encodeRecords]
  have hfold := history.fold_of_false (by simp) (fun s => s.stacks 4)
    (fun out bits => retain bits out) (fun _ _ _ h => h)
  rw [fold_retain, hout, appendEncoded_encodeRecords] at hfold
  refine ⟨n, final, hn, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [invariant, final, RecordPrograms.state, ports] using hnext
  · simp [final, RecordPrograms.state, ports]
  · simp [final, RecordPrograms.state, ports]
  · simpa [final, RecordPrograms.state, ports] using hfold
  · have hany : words.any (fun _ => false) = false := by
      induction words <;> simp_all
    simpa only [hstart, hany, unread_false] using hiter

/-- One fixed finite instruction table for every field size and word width. -/
def program := StructuredCalls.compiled cmd 0 4

theorem program_runsIn (words accum : List (List Bool)) (base : State 6 5)
    (hb : invariant base) (hin : base.stacks 0 = ProgramEncoding.encodeRecords words)
    (hpayload : base.stacks 1 = [])
    (hout : base.stacks 4 = ProgramEncoding.encodeRecords accum) :
    ∃ next, invariant next ∧ next.stacks 0 = [] ∧ next.stacks 1 = [] ∧
      next.stacks 4 = ProgramEncoding.encodeRecords
        ((words.filter PositiveWordProgram.positive).reverse ++ accum) ∧
      RunsIn program (budget words + 1)
        (base.withPC (some program.entry)) (next.withPC none) := by
  obtain ⟨n, next, hn, hi, h0, h1, h4, he⟩ := cmd_eval words accum base hb hin hpayload hout
  exact ⟨next, hi, h0, h1, h4, n + 1, Nat.add_le_add_right hn 1,
    StructuredCalls.compiled_halt_trace he 0 4⟩

theorem budget_le_input (words : List (List Bool)) :
    budget words + 1 ≤ 77 * ((ProgramEncoding.encodeRecords words).length + 1) := by
  have h := RecordPrograms.program_budget_le_input
    (fun bits => 20 * bits.length + 40) words 20 40 (fun _ _ => le_rfl)
  dsimp [budget]
  omega

end SubexponentialSAT.SubexpNodeFilter

end OAI.Algorithms

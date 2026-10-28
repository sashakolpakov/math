import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpUnaryFamilyCallback
import OAI.Algorithms.SubexponentialSAT.ExecLiteralDedupProgram

namespace OAI.Algorithms

/-! A fixed program maps the closed unary table constructor over the actual
width-record stream, restores chunk order, and preserves the scope stream. -/

namespace SubexponentialSAT.SubexpUnaryFamilyProgram

open BitProgram StructuredCalls
open SubexpUnaryFamilyCallback

def ports : RecordPrograms.Ports 16 20 where
  tag := 13
  present := 14
  found := 15
  source := 0
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def Invariant (modulus scope : List Bool) (d : Data) : Prop :=
  Clean d ∧ d.stacks 16 = modulus ∧ d.stacks 19 = scope

@[simp] theorem invariant_state (modulus scope : List Bool) (base : Data)
    (v pr f : Bool) (src payload : List Bool) :
    Invariant modulus scope (RecordPrograms.state ports base v pr f src payload) ↔
      Invariant modulus scope base := by
  simp [Invariant, Clean, RecordPrograms.state, ports]

@[simp] theorem state_output (base : Data) (v pr f : Bool) (src payload : List Bool) :
    (RecordPrograms.state ports base v pr f src payload).stacks 2 = base.stacks 2 := by
  simp [RecordPrograms.state, ports]

def rowTable (modulus width : List Bool) : List Bool :=
  SubexpUnaryFactorTable.table width.length (CounterPrograms.value modulus)

def tables (modulus : List Bool) (widths : List (List Bool)) : List (List Bool) :=
  widths.map (rowTable modulus)

def callbackCost (modulus : List Bool) : ℕ :=
  240 * (CounterPrograms.value modulus + modulus.length + 1) ^ 2

def Effect (modulus width : List Bool) (before after : Data) : Prop :=
  after.stacks 2 = true :: (Encoding.frame (rowTable modulus width) ++ before.stacks 2)

theorem callback_contract (modulus scope : List Bool) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (fun _ => callbackCost modulus) (Invariant modulus scope) (Effect modulus)
      (fun width => width.length ≤ modulus.length) := by
  intro width tail base hw hbase
  let d := RecordPrograms.state ports base false true false tail width.reverse
  have hd : Invariant modulus scope d := (invariant_state _ _ _ _ _ _ _ _).mpr hbase
  obtain ⟨n, hn, next, he, hc, hs, hp, ho, hm, hscope, ht, hpr, hf⟩ :=
    callback_eval width modulus d (by simp [d, RecordPrograms.state, ports]) hd.2.1 hw hd.1
  have hs' : next.stacks 0 = tail := by simpa [d, RecordPrograms.state, ports] using hs
  have hend : RecordPrograms.state ports next false true false tail [] = next :=
    RecordPrograms.state_eq_self ports next false true false _ [] ht hpr hf hs' hp
  refine ⟨n, next, hn, ⟨hc, hm, hscope.trans hd.2.2⟩, ?_, ?_⟩
  · simpa [Effect, rowTable, d] using ho
  · rw [hend]
    exact he

theorem visits_output (modulus : List Bool) {widths : List (List Bool)} {base next : Data}
    (h : RecordPrograms.Visits (fun _ => false) (Effect modulus) widths base next)
    (acc : List (List Bool)) (hacc : base.stacks 2 = Encoding.encodeList id acc) :
    next.stacks 2 = Encoding.encodeList id ((tables modulus widths).reverse ++ acc) := by
  induction h generalizing acc with
  | nil base => simpa [tables] using hacc
  | hit ht he => simp at ht
  | @miss width rest base middle next ht he history ih =>
      have hm : middle.stacks 2 = Encoding.encodeList id (rowTable modulus width :: acc) := by
        simpa [Effect, hacc, Encoding.encodeList] using he
      have hnext := ih (rowTable modulus width :: acc) hm
      simpa [tables, List.reverse_cons, List.append_assoc] using hnext

abbrev scan : Cmd 16 20 := RecordPrograms.iterate ports callback

theorem scan_eval (modulus scope : List Bool) (widths acc : List (List Bool))
    (base : Data) (hw : ∀ width ∈ widths, width.length ≤ modulus.length)
    (valid : Invariant modulus scope base)
    (hacc : base.stacks 2 = Encoding.encodeList id acc) (v pr f : Bool) :
    ∃ n next, n ≤ 3 + RecordPrograms.budget (fun _ => callbackCost modulus) widths ∧
      Invariant modulus scope next ∧
      next.stacks 2 = Encoding.encodeList id ((tables modulus widths).reverse ++ acc) ∧
      Eval scan n (RecordPrograms.state ports base v pr f (Encoding.encodeList id widths) [])
        (RecordPrograms.state ports next false true false [] []) := by
  obtain ⟨n, next, hn, hnext, hh, he⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (fun _ => callbackCost modulus)
    (Invariant modulus scope) (Effect modulus) (fun width => width.length ≤ modulus.length)
    (callback_contract modulus scope) widths [] base hw valid v pr f
  have hany : widths.any (fun _ => false) = false := by
    induction widths <;> simp_all
  refine ⟨n, next, hn, hnext, visits_output modulus hh acc hacc, ?_⟩
  simpa [scan, hany, SubexpNormalizeProgram.unread_false] using he

def reverseStack : Fin 4 → Fin 20 := ![2, 3, 0, 1]
theorem reverseStack_injective : Function.Injective reverseStack := by decide

abbrev reverseCall : Cmd 16 20 := .call (ProgramLinking.liftProgram
  SubexpNormalizeProgram.reverseRecordsProgram emitReg reverseStack)

theorem reverseCall_eval (records acc : List (List Bool)) (d : Data)
    (hsource : d.stacks 2 = Encoding.encodeList id records)
    (houtput : d.stacks 0 = Encoding.encodeList id acc) (hpayload : d.stacks 1 = []) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length, ∃ e : Data,
      Eval reverseCall n d e ∧
      e.stacks 0 = Encoding.encodeList id (records.reverse ++ acc) ∧
      e.stacks 1 = [] ∧ e.stacks 2 = [] ∧
      (∀ i : Fin 20, 3 ≤ i.val → e.stacks i = d.stacks i) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 13) (d.regs 14) (d.regs 15)
    (Encoding.encodeList id records) (d.stacks 3) (Encoding.encodeList id acc) []
  have ha : a = projectState emitReg reverseStack d := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ reverseStack,
 hsource, houtput, hpayload]
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records acc []
    (d.stacks 3) (d.regs 13) (d.regs 14) (d.regs 15)
  simp only [List.append_nil] at ht
  change Trace SubexpNormalizeProgram.reverseRecordsProgram n
    (a.withPC _) _ at ht
  rw [ha] at ht
  have he := eval_call_from_state SubexpNormalizeProgram.reverseRecordsProgram
    emitReg reverseStack d emitReg_injective reverseStack_injective ht
  let b := SubexpNormalizeProgram.filterState false true false [] (d.stacks 3)
    (Encoding.encodeList id (records.reverse ++ acc)) []
  let e := embedState emitReg reverseStack d b
  have hs (i : Fin 4) : e.stacks (reverseStack i) = b.stacks i :=
    embedState_stack _ _ _ _ reverseStack_injective i
  refine ⟨n, hn, e, he, ?_, ?_, ?_, ?_⟩
  · exact hs 2
  · exact hs 3
  · exact hs 0
  · intro i hi
    by_cases h3 : i = 3
    · subst i; exact hs 1
    · apply embedState_stack_frame
      rintro ⟨j, hj⟩
      fin_cases j <;> simp [reverseStack] at hj <;> subst i <;> simp_all

abbrev pushFalse (stack : Fin 20) : Cmd 16 20 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push stack 0))

def pushed (stack : Fin 20) (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks stack (false :: d.stacks stack)⟩

theorem pushFalse_eval (stack : Fin 20) (d : Data) : Eval (pushFalse stack) 2 d (pushed stack d) := by
  let middle : Data := ⟨Function.update d.regs 0 false, d.stacks⟩
  have h₁ : Eval (RecordPrograms.atom (.set 0 false)) 1 d middle := by
    apply Eval.base
    simpa [middle, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.set (r := 16) (s := 20) 0 false) d
  have h₂ : Eval (RecordPrograms.atom (.push stack 0)) 1 middle (pushed stack d) := by
    apply Eval.base
    simpa [middle, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 16) (s := 20) stack 0) middle
  exact h₁.seq h₂

theorem tables_encoding_length (modulus : List Bool) (widths : List (List Bool)) :
    (Encoding.encodeList id (tables modulus widths)).length =
      (2 * CounterPrograms.value modulus + 2) * widths.length + 1 := by
  induction widths with
  | nil => simp [tables]
  | cons width rest ih =>
      simp only [tables, List.map_cons, Encoding.length_encodeList_cons, id_eq,
        rowTable, SubexpUnaryFactorTable.table_length, List.length_cons] at *
      nlinarith

def Ready (d : Data) : Prop := Clean d ∧ d.stacks 1 = [] ∧ d.stacks 2 = []

abbrev command : Cmd 16 20 := .seq (pushFalse 2) (.seq scan (.seq (pushFalse 0) reverseCall))

theorem command_eval (modulus : List Bool) (widths : List (List Bool)) (d : Data)
    (hp : d.stacks 16 = modulus) (hs : d.stacks 0 = Encoding.encodeList id widths)
    (hw : ∀ width ∈ widths, width.length ≤ modulus.length) (hr : Ready d) :
    ∃ n ≤ 399 * (CounterPrograms.value modulus + modulus.length + 1) ^ 2 *
        ((Encoding.encodeList id widths).length + 1), ∃ e : Data,
      Eval command n d e ∧ Ready e ∧ e.stacks 16 = modulus ∧ e.stacks 19 = d.stacks 19 ∧
      e.stacks 0 = Encoding.encodeList id (tables modulus widths) := by
  rcases hr with ⟨hc, h1, h2⟩
  let a := pushed 2 d
  have ha : Invariant modulus (d.stacks 19) a := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [a, pushed, Clean] using hc
    · simpa [a, pushed] using hp
    · simp [a, pushed]
  have ha2 : a.stacks 2 = Encoding.encodeList id [] := by simp [a, pushed, h2, Encoding.encodeList]
  obtain ⟨n, next, hn, hnext, hout, hscan⟩ := scan_eval modulus (d.stacks 19) widths [] a hw ha ha2
    (a.regs 13) (a.regs 14) (a.regs 15)
  have hstart : RecordPrograms.state ports a (a.regs 13) (a.regs 14) (a.regs 15)
      (Encoding.encodeList id widths) [] = a := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa [a, pushed, ports] using hs
    · simpa [a, pushed, ports] using h1
  rw [hstart] at hscan
  let b := RecordPrograms.state ports next false true false [] []
  let c := pushed 0 b
  have hcInv : Invariant modulus (d.stacks 19) c := by
    simpa [c, pushed, b, Invariant, Clean, RecordPrograms.state, ports] using hnext
  have hc2 : c.stacks 2 = Encoding.encodeList id (tables modulus widths).reverse := by
    simpa [c, pushed, b] using hout
  have hc0 : c.stacks 0 = Encoding.encodeList id [] := by
    simp [c, pushed, b, RecordPrograms.state, ports, Encoding.encodeList]
  have hc1 : c.stacks 1 = [] := by simp [c, pushed, b, RecordPrograms.state, ports]
  obtain ⟨m, hm, e, he, he0, he1, he2, hef⟩ :=
    reverseCall_eval (tables modulus widths).reverse [] c hc2 hc0 hc1
  have hbudget := RecordPrograms.program_budget_le_input
    (fun _ => callbackCost modulus) widths 0 (callbackCost modulus) (by intro bits hi; simp)
  have hlength := Encoding.length_encodeList_lower id widths
  rw [ExecLiteralDedupProgram.encoded_reverse_length, tables_encoding_length] at hm
  have hQ : CounterPrograms.value modulus + 1 ≤
      (CounterPrograms.value modulus + modulus.length + 1) ^ 2 := by
    calc
      CounterPrograms.value modulus + 1 ≤ CounterPrograms.value modulus + modulus.length + 1 := by omega
      _ ≤ (CounterPrograms.value modulus + modulus.length + 1) ^ 2 := by
        simpa only [pow_two] using Nat.le_mul_of_pos_right
          (CounterPrograms.value modulus + modulus.length + 1) (by omega :
            0 < CounterPrograms.value modulus + modulus.length + 1)
  have hQpos : 0 < (CounterPrograms.value modulus + modulus.length + 1) ^ 2 := pow_pos (by omega) _
  have hnBudget : n + 1 ≤ (callbackCost modulus + 17) *
      ((Encoding.encodeList id widths).length + 1) := by
    simpa only [Nat.zero_add, ProgramEncoding.encodeRecords] using
      (show n + 1 ≤ (0 + callbackCost modulus + 17) *
        ((ProgramEncoding.encodeRecords widths).length + 1) from by omega)
  have hR : (Encoding.encodeList id widths).length + 1 ≤
      (CounterPrograms.value modulus + modulus.length + 1) ^ 2 *
        ((Encoding.encodeList id widths).length + 1) :=
    Nat.le_mul_of_pos_left _ hQpos
  refine ⟨2 + (n + (2 + m)), ?_, e, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [callbackCost] at hnBudget
    nlinarith [Nat.mul_le_mul_right ((Encoding.encodeList id widths).length + 1) hQ,
      Nat.mul_le_mul_left (2 * CounterPrograms.value modulus + 2) hlength]
  · exact (pushFalse_eval 2 d).seq (hscan.seq ((pushFalse_eval 0 b).seq he))
  · exact ⟨fun i hi => (hef (bankStack i) (by simp [bankStack])).trans (hcInv.1 i hi), he1, he2⟩
  · exact (hef 16 (by decide)).trans hcInv.2.1
  · exact (hef 19 (by decide)).trans hcInv.2.2
  · simpa only [List.reverse_reverse, List.append_nil] using he0

def program := compiled command 0 0

theorem program_runsIn (modulus : List Bool) (widths : List (List Bool)) (d : Data)
    (hp : d.stacks 16 = modulus) (hs : d.stacks 0 = Encoding.encodeList id widths)
    (hw : ∀ width ∈ widths, width.length ≤ modulus.length) (hr : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 16 = modulus ∧ e.stacks 19 = d.stacks 19 ∧
      e.stacks 0 = Encoding.encodeList id (tables modulus widths) ∧
      RunsIn program (400 * (CounterPrograms.value modulus + modulus.length + 1) ^ 2 *
        ((Encoding.encodeList id widths).length + 1))
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨n, hn, e, he, hr, hp, hscope, hout⟩ := command_eval modulus widths d hp hs hw hr
  refine ⟨e, hr, hp, hscope, hout, n + 1, ?_, compiled_halt_trace he 0 0⟩
  have hpos : 0 < (CounterPrograms.value modulus + modulus.length + 1) ^ 2 *
      ((Encoding.encodeList id widths).length + 1) := Nat.mul_pos (pow_pos (by omega) _) (by omega)
  nlinarith

theorem primitive_execution (modulus : List Bool) (widths : List (List Bool)) (d : Data)
    (hp : d.stacks 16 = modulus) (hs : d.stacks 0 = Encoding.encodeList id widths)
    (hw : ∀ width ∈ widths, width.length ≤ modulus.length) (hr : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 16 = modulus ∧ e.stacks 19 = d.stacks 19 ∧
      e.stacks 0 = Encoding.encodeList id (tables modulus widths) ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (400 * (CounterPrograms.value modulus + modulus.length + 1) ^ 2 *
          ((Encoding.encodeList id widths).length + 1)))
        (primitiveCfg program (d.withPC (some program.entry)))
        (primitiveCfg program (e.withPC none)) := by
  obtain ⟨e, hr, hp, hscope, hout, hrun⟩ := program_runsIn modulus widths d hp hs hw hr
  exact ⟨e, hr, hp, hscope, hout, BitProgram.primitive_execution program hrun⟩

end SubexponentialSAT.SubexpUnaryFamilyProgram

end OAI.Algorithms

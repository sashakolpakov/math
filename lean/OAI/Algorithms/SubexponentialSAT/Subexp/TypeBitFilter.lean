import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TypeBitProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPreparation
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! A fixed filter of framed records by a bit at a runtime unary index.
The source and index are preserved. The final reversal retains input order. -/

namespace SubexponentialSAT.Subexp.TypeBitFilter

open BitProgram StructuredCalls TupleProgram
open BlockSearchPreparation (restrictState lifted_call)

abbrev Data := State 8 11

def ports : RecordPrograms.Ports 8 11 :=
  ⟨0,1,2,2,3,by decide,by decide,by decide,by decide⟩

def emitPorts : RecordPrograms.Ports 8 11 :=
  ⟨3,4,6,3,9,by decide,by decide,by decide,by decide⟩

def scanRegisters : Fin 3 → Fin 8 := ![3,4,5]
def scanStacks : Fin 2 → Fin 11 := ![7,4]
theorem scanRegisters_injective : Function.Injective scanRegisters := by decide
theorem scanStacks_injective : Function.Injective scanStacks := by decide

def scanned (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 3 false) 4 false) 5
      ((a.stacks 4).getD (a.stacks 7).length false),
    Function.update (Function.update a.stacks 7 []) 4 []⟩

abbrev scan : Cmd 8 11 := .call (ProgramLinking.liftProgram TypeBitProgram.program scanRegisters scanStacks)

theorem scan_eval (a : Data) : Eval scan (TypeBitProgram.cost (a.stacks 7) (a.stacks 4)) a (scanned a) := by
  let before : State 3 2 := ⟨fun i => a.regs (scanRegisters i), ParserProgram.pair (a.stacks 7) (a.stacks 4)⟩
  let after : State 3 2 := ⟨TypeBitProgram.resultRegs ((a.stacks 4).getD (a.stacks 7).length false),
    ParserProgram.pair [] []⟩
  have hi : embedState scanRegisters scanStacks a before = a := by
    apply SubexpScanPrimitives.embedState_eq _ _ scanRegisters_injective scanStacks_injective
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intros; rfl
  have ho : embedState scanRegisters scanStacks a after = scanned a := by
    apply SubexpScanPrimitives.embedState_eq _ _ scanRegisters_injective scanStacks_injective
    · intro i; fin_cases i <;> simp [scanned,after,scanRegisters,TypeBitProgram.resultRegs]
    · intro i; fin_cases i <;> simp [scanned,after,scanStacks,ParserProgram.pair]
    · intro i hi
      have h3 : i ≠ 3 := fun h => hi ⟨0,by simpa [scanRegisters] using h.symm⟩
      have h4 : i ≠ 4 := fun h => hi ⟨1,by simpa [scanRegisters] using h.symm⟩
      have h5 : i ≠ 5 := fun h => hi ⟨2,by simpa [scanRegisters] using h.symm⟩
      simp [scanned,h3,h4,h5]
    · intro i hi
      have h7 : i ≠ 7 := fun h => hi ⟨0,by simpa [scanStacks] using h.symm⟩
      have h4 : i ≠ 4 := fun h => hi ⟨1,by simpa [scanStacks] using h.symm⟩
      simp [scanned,h7,h4]
  have hlocal : Trace TypeBitProgram.program (TypeBitProgram.cost (a.stacks 7) (a.stacks 4))
      (before.withPC (some TypeBitProgram.program.entry)) (after.withPC none) :=
    TypeBitProgram.trace (a.stacks 7) (a.stacks 4) (fun i => a.regs (scanRegisters i))
  have ht := eval_call_lifted TypeBitProgram.program scanRegisters scanStacks a
    scanRegisters_injective scanStacks_injective hlocal
  change Eval scan _ (embedState scanRegisters scanStacks a before)
    (embedState scanRegisters scanStacks a after) at ht
  simpa only [hi,ho] using ht

def copied (src dst : Fin 11) (a : Data) : Data :=
  ⟨readRegs a.regs 3 4 none,StackRoutines.copyStacks src dst a.stacks⟩
def transferred (src dst : Fin 11) (a : Data) : Data :=
  ⟨readRegs a.regs 3 4 none,StackRoutines.transferStacks src dst a.stacks⟩
def cleared (src : Fin 11) (a : Data) : Data :=
  ⟨readRegs a.regs 3 4 none,StackRoutines.clearStacks src a.stacks⟩

abbrev select (keep : Bool) : Cmd 8 11 :=
  if keep then .base .skip else .base (.atom (.bnot 5 5))
def selected (keep : Bool) (a : Data) : Data :=
  ⟨Function.update a.regs 5 (decide (a.regs 5 = keep)),a.stacks⟩

theorem select_eval (keep : Bool) (a : Data) :
    Eval (select keep) (if keep then 0 else 1) a (selected keep a) := by
  cases keep with
  | false =>
      have h := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.bnot (5 : Fin 8) 5) a)
      simpa [select,selected,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using h
  | true =>
      have he : selected true a = a := by
        apply congrArg₂ StructuredProgram.State.mk
        · funext i
          by_cases hi : i = 5 <;> simp [hi]
        · rfl
      rw [he]
      exact .base (.skip a)

abbrev emit : Cmd 8 11 :=
  .seq (pushConst 9 3 false) (.seq (escape emitPorts) (pushConst 9 3 true))
def emitted (a : Data) : Data :=
  pushedState 9 3 true (escapedState emitPorts (pushedState 9 3 false a))

theorem emit_eval (a : Data) : Eval emit (5 * (a.stacks 3).length + 7) a (emitted a) := by
  have h := (pushConst_eval 9 3 false a).seq
    ((escape_eval_state emitPorts (pushedState 9 3 false a)).seq
      (pushConst_eval 9 3 true (escapedState emitPorts (pushedState 9 3 false a))))
  convert h using 1 <;> simp [emitted,emitPorts,pushedState] ; omega

abbrev callback (keep : Bool) : Cmd 8 11 :=
  .seq (.call (StackRoutines.copyProgram 3 6 5 3 4))
    (.seq (.call (StackRoutines.transferProgram 6 4 3 4))
      (.seq (.call (StackRoutines.copyProgram 1 7 5 3 4))
        (.seq scan (.seq (select keep)
          (.ite 5 emit (.call (StackRoutines.clearProgram 3 3 4)))))))

def invariant (source index : List Bool) (a : Data) : Prop :=
  a.stacks 0 = source ∧ a.stacks 1 = index ∧ a.stacks 4 = [] ∧ a.stacks 5 = [] ∧
    a.stacks 6 = [] ∧ a.stacks 7 = [] ∧ a.stacks 8 = [] ∧ a.stacks 10 = []

def test (keep : Bool) (index : ℕ) (bits : List Bool) : Bool := decide (bits.getD index false = keep)

def callbackCost (index : ℕ) (bits : List Bool) : ℕ := 20 * bits.length + 12 * index + 40

theorem callback_contract (keep : Bool) (source index : List Bool) :
    RecordPrograms.CallbackContractWith ports (callback keep) (fun _ => false)
      (callbackCost index.length) (invariant source index)
      (SubexpNormalizeProgram.FilterEffect 9 (test keep index.length)) := by
  intro bits tail base hi
  rcases hi with ⟨hi0,hi1,hi4,hi5,hi6,hi7,hi8,hi10⟩
  let a := RecordPrograms.state ports base false true false tail bits.reverse
  let b := copied 3 6 a
  let c := transferred 6 4 b
  let d := copied 1 7 c
  let e := scanned d
  let f := selected keep e
  have h1 := copy_eval 3 6 5 3 4 (by decide) (by decide) (by decide) (by decide) a
    (by simpa [a,ports,RecordPrograms.state] using hi5)
  have h2 := transfer_eval 6 4 3 4 (by decide) (by decide) b
  have h3 := copy_eval 1 7 5 3 4 (by decide) (by decide) (by decide) (by decide) c
    (by simp [c,b,a,copied,transferred,StackRoutines.transferStacks,StackRoutines.copyStacks,
      ports,RecordPrograms.state,hi5])
  have h4 := scan_eval d
  have h5 := select_eval keep e
  have ha3 : a.stacks 3 = bits.reverse := by simp [a,ports,RecordPrograms.state]
  have hb6 : b.stacks 6 = bits.reverse := by
    simp [b,a,copied,StackRoutines.copyStacks,ports,RecordPrograms.state,hi6]
  have hc1 : c.stacks 1 = index := by
    simp [c,b,a,transferred,copied,StackRoutines.transferStacks,StackRoutines.copyStacks,
      ports,RecordPrograms.state,hi1]
  have hd4 : d.stacks 4 = bits := by
    simp [d,c,b,a,copied,transferred,StackRoutines.transferStacks,StackRoutines.copyStacks,
      ports,RecordPrograms.state,hi4,hi6]
  have hd7 : d.stacks 7 = index := by
    simp [d,c,b,a,copied,transferred,StackRoutines.transferStacks,StackRoutines.copyStacks,
      ports,RecordPrograms.state,hi7,hi1]
  have hf3 : f.stacks 3 = bits.reverse := by
    simp [f,e,d,c,b,a,selected,scanned,copied,transferred,
      StackRoutines.transferStacks,StackRoutines.copyStacks,ports,RecordPrograms.state]
  have hf5 : f.regs 5 = test keep index.length bits := by
    simp [f,e,selected,scanned,hd4,hd7,test]
  have hfI : invariant source index f := by
    simp [invariant,f,e,d,c,b,a,selected,scanned,copied,transferred,
      StackRoutines.transferStacks,StackRoutines.copyStacks,
      ports,RecordPrograms.state,hi0,hi1,hi5,hi8,hi10]
  have hf9 : f.stacks 9 = base.stacks 9 := by
    simp [f,e,d,c,b,a,selected,scanned,copied,transferred,
      StackRoutines.transferStacks,StackRoutines.copyStacks,ports,RecordPrograms.state]
  have hfFlags : f.regs 0 = false ∧ f.regs 1 = true ∧ f.regs 2 = false ∧ f.stacks 2 = tail := by
    simp [f,e,d,c,b,a,selected,scanned,copied,transferred,readRegs,
      StackRoutines.transferStacks,StackRoutines.copyStacks,ports,RecordPrograms.state]
  rcases hfI with ⟨hfI0,hfI1,hfI4,hfI5,hfI6,hfI7,hfI8,hfI10⟩
  rcases hfFlags with ⟨hfr0,hfr1,hfr2,hf2⟩
  have hcost := TypeBitProgram.cost_le (d.stacks 7) (d.stacks 4)
  simp only [hd4,hd7] at hcost
  cases hk : test keep index.length bits with
  | false =>
      let g := cleared 3 f
      have h6 := clear_eval 3 3 4 f
      have hb : Eval (.ite 5 emit (.call (StackRoutines.clearProgram 3 3 4)))
          (2 * (f.stacks 3).length + 3 + 1) f g := Eval.ite_false (hf5.trans hk) h6
      have he := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq hb))))
      refine ⟨(7 * (a.stacks 3).length + 5) + ((3 * (b.stacks 6).length + 3) +
        ((7 * (c.stacks 1).length + 5) + (TypeBitProgram.cost (d.stacks 7) (d.stacks 4) +
          ((if keep then 0 else 1) + (2 * (f.stacks 3).length + 3 + 1))))),g,?_,?_,?_,?_⟩
      · simp only [ha3,hb6,hc1,hd4,hd7,hf3,List.length_reverse]
        dsimp [callbackCost]
        split <;> omega
      · simp [invariant,g,cleared,StackRoutines.clearStacks,hfI0,hfI1,hfI4,hfI5,hfI6,hfI7,hfI8,hfI10]
      · simp [SubexpNormalizeProgram.FilterEffect,hk,g,cleared,StackRoutines.clearStacks,hf9]
      · have hg : RecordPrograms.state ports g false true false tail [] = g := by
          apply RecordPrograms.state_eq_self <;>
            simp [g,cleared,readRegs,StackRoutines.clearStacks,ports,hfr0,hfr1,hfr2,hf2]
        rw [hg]
        exact he
  | true =>
      let g := emitted f
      have h6 := emit_eval f
      have hb : Eval (.ite 5 emit (.call (StackRoutines.clearProgram 3 3 4)))
          (5 * (f.stacks 3).length + 7 + 1) f g := Eval.ite_true (hf5.trans hk) h6
      have he := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq hb))))
      refine ⟨(7 * (a.stacks 3).length + 5) + ((3 * (b.stacks 6).length + 3) +
        ((7 * (c.stacks 1).length + 5) + (TypeBitProgram.cost (d.stacks 7) (d.stacks 4) +
          ((if keep then 0 else 1) + (5 * (f.stacks 3).length + 7 + 1))))),g,?_,?_,?_,?_⟩
      · simp only [ha3,hb6,hc1,hd4,hd7,hf3,List.length_reverse]
        dsimp [callbackCost]
        split <;> omega
      · simp [invariant,g,emitted,pushedState,emitPorts,
          hfI0,hfI1,hfI4,hfI5,hfI6,hfI7,hfI8,hfI10]
      · simp [SubexpNormalizeProgram.FilterEffect,hk,g,emitted,pushedState,
          emitPorts,hf3,hf9,frame_eq_escaped,List.append_assoc]
      · have hg : RecordPrograms.state ports g false true false tail [] = g := by
          apply RecordPrograms.state_eq_self <;>
            simp [g,emitted,pushedState,emitPorts,readRegs,
              ports,hfr0,hfr1,hfr2,hf2]
        rw [hg]
        exact he

def reverseRegisters : Fin 3 → Fin 8 := ![3,4,6]
def reverseStacks : Fin 4 → Fin 11 := ![9,0,10,3]
theorem reverseRegisters_injective : Function.Injective reverseRegisters := by decide
theorem reverseStacks_injective : Function.Injective reverseStacks := by decide

abbrev reverse : Cmd 8 11 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram reverseRegisters reverseStacks)

def reversed (a : Data) (words : Records) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 3 false) 4 true) 6 false,
    Function.update (Function.update (Function.update a.stacks 9 []) 10
      (ProgramEncoding.encodeRecords words.reverse)) 3 []⟩

theorem reverse_eval (a : Data) (words : Records)
    (h9 : a.stacks 9 = ProgramEncoding.encodeRecords words)
    (h10 : a.stacks 10 = [false]) (h3 : a.stacks 3 = []) :
    ∃ n ≤ 10 * (ProgramEncoding.encodeRecords words).length, Eval reverse n a (reversed a words) := by
  have hi : restrictState reverseRegisters reverseStacks a =
      SubexpNormalizeProgram.filterState (a.regs 3) (a.regs 4) (a.regs 6)
        (Encoding.encodeList id words ++ []) (a.stacks 0) (Encoding.encodeList id []) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;>
        simp [reverseStacks,h9,h10,h3,
          ProgramEncoding.encodeRecords,Encoding.encodeList]
  obtain ⟨n,hn,he⟩ := lifted_call SubexpNormalizeProgram.reverseRecordsProgram reverseRegisters reverseStacks
    reverseRegisters_injective reverseStacks_injective a
    (SubexpNormalizeProgram.filterState false true false [] (a.stacks 0)
      (Encoding.encodeList id (words.reverse ++ [])) [])
    (10 * (ProgramEncoding.encodeRecords words).length)
    (by
      rw [hi]
      exact SubexpNormalizeProgram.reverseRecords_runsIn words [] [] (a.stacks 0)
        (a.regs 3) (a.regs 4) (a.regs 6))
  have ho : embedState reverseRegisters reverseStacks a
      (SubexpNormalizeProgram.filterState false true false [] (a.stacks 0)
        (Encoding.encodeList id (words.reverse ++ [])) []) = reversed a words := by
    apply SubexpScanPrimitives.embedState_eq _ _ reverseRegisters_injective reverseStacks_injective
    · intro i; fin_cases i <;> simp [reverseRegisters,reversed,SubexpNormalizeProgram.filterState]
    · intro i; fin_cases i <;>
        simp [reverseStacks,reversed,SubexpNormalizeProgram.filterState,ProgramEncoding.encodeRecords]
    · intro i hi
      have h3 : i ≠ 3 := fun h => hi ⟨0,by simpa [reverseRegisters] using h.symm⟩
      have h4 : i ≠ 4 := fun h => hi ⟨1,by simpa [reverseRegisters] using h.symm⟩
      have h6 : i ≠ 6 := fun h => hi ⟨2,by simpa [reverseRegisters] using h.symm⟩
      simp [reversed,h3,h4,h6]
    · intro i hi
      have h9 : i ≠ 9 := fun h => hi ⟨0,by simpa [reverseStacks] using h.symm⟩
      have h10 : i ≠ 10 := fun h => hi ⟨2,by simpa [reverseStacks] using h.symm⟩
      have h3 : i ≠ 3 := fun h => hi ⟨3,by simpa [reverseStacks] using h.symm⟩
      simp [reversed,h9,h10,h3]
  exact ⟨n,hn,by simpa only [ho] using he⟩

abbrev command (keep : Bool) : Cmd 8 11 :=
  .seq (.call (StackRoutines.copyProgram 0 2 5 3 4))
    (.seq (pushConst 9 3 false)
      (.seq (RecordPrograms.iterate ports (callback keep))
        (.seq (pushConst 10 3 false) reverse)))

def program (keep : Bool) := compiled (command keep) 0 10

def inputState (words : Records) (index : List Bool) (regs : Fin 8 → Bool) : Data :=
  ⟨regs,fun i => if i = 0 then ProgramEncoding.encodeRecords words else if i = 1 then index else []⟩

def outputState (keep : Bool) (words : Records) (index : List Bool) (regs : Fin 8 → Bool) : Data :=
  ⟨regs,fun i => if i = 0 then ProgramEncoding.encodeRecords words else if i = 1 then index
    else if i = 10 then ProgramEncoding.encodeRecords (words.filter (test keep index.length)) else []⟩

def budget (keep : Bool) (words : Records) (index : ℕ) : ℕ :=
  7 * (ProgramEncoding.encodeRecords words).length + RecordPrograms.budget (callbackCost index) words +
    10 * (ProgramEncoding.encodeRecords ((words.filter (test keep index)).reverse)).length + 13

theorem program_runsIn (keep : Bool) (words : Records) (index : List Bool) (regs : Fin 8 → Bool) :
    ∃ nextRegs, RunsIn (program keep) (budget keep words index.length)
      ((inputState words index regs).withPC (some (program keep).entry))
      ((outputState keep words index nextRegs).withPC none) := by
  let a := inputState words index regs
  let b := copied 0 2 a
  let c := pushedState 9 3 false b
  have h1 := copy_eval 0 2 5 3 4 (by decide) (by decide) (by decide) (by decide) a
    (by simp [a,inputState])
  have h2 := pushConst_eval 9 3 false b
  have hc : invariant (ProgramEncoding.encodeRecords words) index c := by
    simp [invariant,c,b,a,copied,StackRoutines.copyStacks,inputState]
  have hc9 : c.stacks 9 = Encoding.encodeList id [] := by
    simp [c,b,a,copied,StackRoutines.copyStacks,inputState,Encoding.encodeList]
  obtain ⟨n,next,hn,hnext,history,he⟩ := RecordPrograms.iterate_run_with ports (callback keep)
    (fun _ => false) (callbackCost index.length) (invariant (ProgramEncoding.encodeRecords words) index)
    (SubexpNormalizeProgram.FilterEffect 9 (test keep index.length))
    (callback_contract keep _ index) words [] c hc (c.regs 0) (c.regs 1) (c.regs 2)
  have hstart : RecordPrograms.state ports c (c.regs 0) (c.regs 1) (c.regs 2)
      (Encoding.encodeList id words ++ []) [] = c := by
    apply RecordPrograms.state_eq_self <;>
      simp [c,b,a,copied,StackRoutines.copyStacks,inputState,ports,
        ProgramEncoding.encodeRecords]
  let d := RecordPrograms.state ports next false true false [] []
  have he' : Eval (RecordPrograms.iterate ports (callback keep)) n c d := by
    simpa only [hstart,show words.any (fun _ => false) = false by simp,unread_false,d] using he
  have hd9 : d.stacks 9 = ProgramEncoding.encodeRecords ((words.filter (test keep index.length)).reverse) := by
    have h := SubexpNormalizeProgram.filterVisits_result 9 (test keep index.length) history [] hc9
    simpa [d,ports,RecordPrograms.state,ProgramEncoding.encodeRecords] using h
  let e := pushedState 10 3 false d
  have h4 := pushConst_eval 10 3 false d
  have hi : invariant (ProgramEncoding.encodeRecords words) index d := by
    rcases hnext with ⟨h0,h1,h4,h5,h6,h7,h8,h10⟩
    simp [invariant,d,ports,RecordPrograms.state,h0,h1,h4,h5,h6,h7,h8,h10]
  obtain ⟨m,hm,h5⟩ := reverse_eval e ((words.filter (test keep index.length)).reverse)
    (by simpa [e,pushedState] using hd9)
    (by simp [e,hi.2.2.2.2.2.2.2])
    (by simp [e,d,ports,RecordPrograms.state])
  have hout : reversed e ((words.filter (test keep index.length)).reverse) =
      outputState keep words index (reversed e ((words.filter (test keep index.length)).reverse)).regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    rcases hi with ⟨h0,h1,h4,h5,h6,h7,h8,h10⟩
    have hd2 : d.stacks 2 = [] := by simp [d,ports,RecordPrograms.state]
    have hd3 : d.stacks 3 = [] := by simp [d,ports,RecordPrograms.state]
    fin_cases i <;>
      simp [e,h0,h1,hd2,h4,h5,h6,h7,h8,h10]
  rw [hout] at h5
  have ht := h1.seq (h2.seq (he'.seq (h4.seq h5)))
  refine ⟨_,_,?_,compiled_halt_trace ht 0 10⟩
  simp only [a,inputState]
  dsimp [budget]
  omega

end SubexponentialSAT.Subexp.TypeBitFilter

end OAI.Algorithms

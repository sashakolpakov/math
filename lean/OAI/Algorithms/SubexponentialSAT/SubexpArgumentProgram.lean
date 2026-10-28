import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRecordScan
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentCode
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-!
# Finite-control serialization of marked-incidence arguments

The raw-list ABI is `Encoding.encodeList id` of record bodies
`frame key ++ frame coefficient`. Coefficient payloads are opaque bit strings.
The term writer consumes one coefficient frame and a reversed key, restoring
its scratch stacks. All loops below execute fixed Boolean/stack instructions.
-/

namespace SubexponentialSAT.SubexpArgumentProgram

open BitProgram StructuredCalls
open SubexpRecordScan

abbrev Data := StructuredProgram.State 5 6

private theorem embedState_eq {r s R S : ℕ}
    (reg : Fin r → Fin R) (stack : Fin s → Fin S)
    (hreg : Function.Injective reg) (hstack : Function.Injective stack)
    (frame target : State R S) (source : State r s)
    (hr : ∀ i, target.regs (reg i) = source.regs i)
    (hs : ∀ i, target.stacks (stack i) = source.stacks i)
    (hfr : ∀ j, (¬ ∃ i, reg i = j) → target.regs j = frame.regs j)
    (hfs : ∀ j, (¬ ∃ i, stack i = j) → target.stacks j = frame.stacks j) :
    embedState reg stack frame source = target :=
  embedState_eq_of_ports reg stack frame target source hreg hstack hr hfr hs hfs

def writerRegs (i : Fin 3) : Fin 5 := ⟨i.val, by omega⟩

def destination (outer : Bool) : Fin 6 := if outer then 3 else 5

def writerStacks (outer : Bool) : Fin 4 → Fin 6 :=
  SubexpPostfixControl.quadruple 0 2 (destination outer) 1

theorem writerRegs_injective : Function.Injective writerRegs := by
  intro i j h
  exact Fin.ext (congrArg (fun v : Fin 5 => v.val) h)

theorem writerStacks_injective (outer : Bool) : Function.Injective (writerStacks outer) := by
  cases outer <;> intro i j h <;> fin_cases i <;> fin_cases j <;>
    simp_all [writerStacks, destination, SubexpPostfixControl.quadruple]

/-- The existing postfix literal encoder, relocated to the key/body buffers. -/
abbrev writer (outer : Bool) : Program 5 6 17 :=
  ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram writerRegs (writerStacks outer)

abbrev finishedRegs (regs : Fin 5 → Bool) : Fin 5 → Bool :=
  Function.update (Function.update regs 0 true) 1 false

abbrev afterWriter (outer : Bool) (d : Data) (bits : List Bool) : Data :=
  ⟨finishedRegs d.regs,
    Function.update (Function.update d.stacks 1 []) (destination outer)
      (true :: (Encoding.frame bits ++ d.stacks (destination outer)))⟩

theorem writer_eval (outer : Bool) (d : Data) (bits : List Bool)
    (hkey : d.stacks 1 = bits.reverse) :
    Eval (.call (writer outer)) (5 * bits.length + 7) d (afterWriter outer d bits) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
    (d.stacks 0) (d.stacks 2) (d.stacks (destination outer)) bits.reverse
  let b := SubexpNormalizeProgram.filterState true false (d.regs 2)
    (d.stacks 0) (d.stacks 2)
    (true :: (Encoding.frame bits ++ d.stacks (destination outer))) []
  have ha : embedState writerRegs (writerStacks outer) d a = d := by
    apply embedState_eq _ _ writerRegs_injective (writerStacks_injective outer)
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> simp [a, writerStacks, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple, hkey]
    · intros; rfl
    · intros; rfl
  have hb : embedState writerRegs (writerStacks outer) d b = afterWriter outer d bits := by
    apply embedState_eq _ _ writerRegs_injective (writerStacks_injective outer)
    · intro i; fin_cases i <;>
        simp [ finishedRegs, writerRegs, b, SubexpNormalizeProgram.filterState,
          SubexpPostfixControl.triple]
    · intro i; cases outer <;> fin_cases i <;>
        simp [ writerStacks, destination, b, SubexpNormalizeProgram.filterState,
          SubexpPostfixControl.quadruple]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      simp [ finishedRegs, h0, h1]
    · intro i hi
      have h1 : i ≠ 1 := fun h => hi ⟨3, h.symm⟩
      have hd : i ≠ destination outer := fun h => hi ⟨2, h.symm⟩
      simp [ h1, hd]
  have ht : Trace SubexpNormalizeProgram.emitRecordProgram (5 * bits.length + 7)
      (a.withPC (some SubexpNormalizeProgram.emitRecordProgram.entry)) (b.withPC none) :=
    SubexpNormalizeProgram.emitRecord_trace bits (d.stacks 0) (d.stacks 2)
      (d.stacks (destination outer)) (d.regs 0) (d.regs 1) (d.regs 2)
  have h := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram writerRegs
    (writerStacks outer) d writerRegs_injective (writerStacks_injective outer) ht
  simpa only [writer, ha, hb] using h

abbrev atom (a : StructuredProgram.Atom 5 6) : Cmd 5 6 := .base (.atom a)

/-- Build one inner record, reverse it once, and frame it as a list item.
Stacks: 0 coefficient input; 1 reversed key; 2 preserved; 3 raw-list output;
4 copy scratch; 5 inner-record scratch. Both scratch stacks start empty. -/
abbrev emitTerm : Cmd 5 6 :=
  .seq (.call copyPayload)
    (.seq (.call (writer false))
      (.seq (atom (.pop 5 0 1))
        (.seq (.call (StackRoutines.transferProgram 5 1 0 1)) (.call (writer true)))))

def recordBody (key coefficient : List Bool) : List Bool :=
  Encoding.frame key ++ Encoding.frame coefficient

theorem emitTerm_eval (key coefficient tail spare output : List Bool) (regs : Fin 5 → Bool) :
    Eval emitTerm (29 * coefficient.length + 21 * key.length + 45)
      (recordState regs (Encoding.frame coefficient ++ tail) key.reverse spare output [] [])
      (recordState (finishedRegs regs) tail [] spare
        (true :: (Encoding.frame (recordBody key coefficient) ++ output)) [] []) := by
  let r₀ := readRegs regs 0 1 none
  let r₁ := finishedRegs r₀
  let r₂ := readRegs r₁ 0 1 (some true)
  let r₃ := readRegs r₂ 0 1 none
  let body := recordBody key coefficient
  have hcopy : Eval (.call copyPayload) (13 * coefficient.length + 11)
      (recordState regs (Encoding.frame coefficient ++ tail) key.reverse spare output [] [])
      (recordState r₀ tail key.reverse spare output [] (Encoding.frame coefficient)) := by
    simpa [afterPayload, recordState, r₀] using
      copyPayload_eval (recordState regs (Encoding.frame coefficient ++ tail)
        key.reverse spare output [] []) coefficient tail rfl rfl
  have hkey : Eval (.call (writer false)) (5 * key.length + 7)
      (recordState r₀ tail key.reverse spare output [] (Encoding.frame coefficient))
      (recordState r₁ tail [] spare output [] (true :: body)) := by
    simpa [afterWriter, destination, recordState, r₁, body, recordBody] using
      writer_eval false (recordState r₀ tail key.reverse spare output [] (Encoding.frame coefficient)) key rfl
  have hpop : Eval (atom (.pop 5 0 1)) 1
      (recordState r₁ tail [] spare output [] (true :: body))
      (recordState r₂ tail [] spare output [] body) := by
    have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (5 : Fin 6) (0 : Fin 5) 1)
      (recordState r₁ tail [] spare output [] (true :: body))
    apply Eval.base
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
      recordState, r₂] using h
  have hreverse : Eval (.call (StackRoutines.transferProgram 5 1 0 1)) (3 * body.length + 3)
      (recordState r₂ tail [] spare output [] body)
      (recordState r₃ tail body.reverse spare output [] []) := by
    apply Eval.call
    simpa [ListRegisterProgram.Run, StackRoutines.transferStacks, recordState,
      storage, r₃, StructuredProgram.State.withPC] using
      ListRegisterProgram.transfer_run (5 : Fin 6) 1 (0 : Fin 5) 1
        (by decide) (by decide) r₂ (storage tail [] spare output [] body)
  have hout : Eval (.call (writer true)) (5 * body.length + 7)
      (recordState r₃ tail body.reverse spare output [] [])
      (recordState (finishedRegs r₃) tail [] spare
        (true :: (Encoding.frame body ++ output)) [] []) := by
    simpa [afterWriter, destination, recordState] using
      writer_eval true (recordState r₃ tail body.reverse spare output [] []) body rfl
  have hr : finishedRegs r₃ = finishedRegs regs := by
    funext i
    fin_cases i <;> simp [r₃, r₂, r₁, r₀, finishedRegs, readRegs]
  have hn : (13 * coefficient.length + 11) + ((5 * key.length + 7) +
      (1 + ((3 * body.length + 3) + (5 * body.length + 7)))) =
      29 * coefficient.length + 21 * key.length + 45 := by
    simp only [body, recordBody, List.length_append, Encoding.length_frame]
    omega
  simpa only [emitTerm, hn, hr] using
    Eval.seq hcopy (Eval.seq hkey (Eval.seq hpop (Eval.seq hreverse hout)))

abbrev emitTermProgram := StructuredCalls.compiled emitTerm 0 3

theorem emitTerm_trace (key coefficient tail spare output : List Bool) (regs : Fin 5 → Bool) :
    Trace emitTermProgram (29 * coefficient.length + 21 * key.length + 46)
      ((recordState regs (Encoding.frame coefficient ++ tail) key.reverse spare output [] []).withPC
        (some emitTermProgram.entry))
      ((recordState (finishedRegs regs) tail [] spare
        (true :: (Encoding.frame (recordBody key coefficient) ++ output)) [] []).withPC none) := by
  simpa only [Nat.add_assoc] using
    StructuredCalls.compiled_halt_trace (emitTerm_eval key coefficient tail spare output regs) 0 3

end SubexponentialSAT.SubexpArgumentProgram

end OAI.Algorithms

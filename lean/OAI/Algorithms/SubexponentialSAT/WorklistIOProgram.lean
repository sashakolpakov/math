import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-!
# Concrete input/output adapter for the encoded sparsification worklist

Four Boolean registers and seven Boolean stacks suffice. The core worklist
uses stacks 0--4; source body 5 is preserved and output leaves are returned on
stack 6. Loading copies and reverses the body, then invokes the existing fixed
frame emitter. Unloading performs two transfers to preserve forward order.
-/

namespace SubexponentialSAT.WorklistIOProgram

open BitProgram StructuredProgram StructuredCalls

abbrev Data := StructuredProgram.State 4 7

def zeroRegs : Fin 4 → Bool := fun _ => false

def stackData (pending leaves childA childB tmp body output : List Bool) :
    Fin 7 → List Bool := ![pending, leaves, childA, childB, tmp, body, output]

def workState (regs : Fin 4 → Bool)
    (pending leaves childA childB tmp body output : List Bool) : Data :=
  ⟨regs, stackData pending leaves childA childB tmp body output⟩

/-- Empty core scratch, with source and destination explicitly separated. -/
abbrev ioState (regs : Fin 4 → Bool) (pending leaves body output : List Bool) : Data :=
  workState regs pending leaves [] [] [] body output

private theorem data_ext {a b : Data} (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) :
    a = b := by cases a; cases b; cases hr; cases hs; rfl

abbrev copy (src dst tmp : Fin 7) : StructuredCalls.Cmd 4 7 :=
  .call (StackRoutines.copyProgram src dst tmp 0 1)
abbrev copied (src dst : Fin 7) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

theorem copy_eval (src dst tmp : Fin 7) (d : Data)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (ht : d.stacks tmp = []) :
    StructuredCalls.Eval (copy src dst tmp) (7 * (d.stacks src).length + 5) d (copied src dst d) :=
  .call _ (ListRegisterProgram.copy_run src dst tmp 0 1 hsd hst htd (by decide)
    d.regs d.stacks ht)

abbrev transfer (src dst : Fin 7) : StructuredCalls.Cmd 4 7 :=
  .call (StackRoutines.transferProgram src dst 0 1)
abbrev transferred (src dst : Fin 7) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

theorem transfer_eval (src dst : Fin 7) (d : Data) (hne : src ≠ dst) :
    StructuredCalls.Eval (transfer src dst) (3 * (d.stacks src).length + 3) d
      (transferred src dst d) :=
  .call _ (ListRegisterProgram.transfer_run src dst 0 1 hne (by decide) d.regs d.stacks)

abbrev clear (src : Fin 7) : StructuredCalls.Cmd 4 7 :=
  .call (StackRoutines.clearProgram src 0 1)
abbrev cleared (src : Fin 7) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks src d.stacks⟩

theorem clear_eval (src : Fin 7) (d : Data) :
    StructuredCalls.Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared src d) :=
  .call _ (ListRegisterProgram.clear_run src 0 1 d.regs d.stacks)

abbrev seedLists : StructuredCalls.Cmd 4 7 := .base
  (.seq (.atom (.set 0 false)) (.seq (.atom (.push 0 0)) (.atom (.push 1 0))))

abbrev seeded (d : Data) : Data :=
  ⟨Function.update d.regs 0 false,
    Function.update (Function.update d.stacks 0 (false :: d.stacks 0)) 1 (false :: d.stacks 1)⟩

theorem seedLists_eval (d : Data) : StructuredCalls.Eval seedLists 3 d (seeded d) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 4) false) d).seq
    ((StructuredProgram.Eval.atom (.push (0 : Fin 7) 0) _).seq
      (StructuredProgram.Eval.atom (.push (1 : Fin 7) 0) _))
  apply StructuredCalls.Eval.base
  simpa [seeded, Atom.eval, Atom.instr, State.ofCfg, State.withPC, execInstr] using h

abbrev reset : StructuredCalls.Cmd 4 7 := .base
  (.seq (.atom (.set 0 false)) (.seq (.atom (.set 1 false))
    (.seq (.atom (.set 2 false)) (.atom (.set 3 false)))))

def resetState (d : Data) : Data := ⟨zeroRegs, d.stacks⟩

theorem reset_eval (d : Data) : StructuredCalls.Eval reset 4 d (resetState d) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 4) false) d).seq
    ((StructuredProgram.Eval.atom (.set (1 : Fin 4) false) _).seq
      ((StructuredProgram.Eval.atom (.set (2 : Fin 4) false) _).seq
        (StructuredProgram.Eval.atom (.set (3 : Fin 4) false) _)))
  apply StructuredCalls.Eval.base
  convert h using 1
  apply data_ext
  · funext i
    fin_cases i <;>
      simp [resetState, zeroRegs, Atom.eval, Atom.instr, State.ofCfg, execInstr]
  · rfl

def writerRegs : Fin 3 → Fin 4 := Fin.castAdd 1
def writerStacks : Fin 4 → Fin 7 := ![5, 2, 0, 3]

theorem writerRegs_injective : Function.Injective writerRegs := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 4 => k.val) h)

theorem writerStacks_injective : Function.Injective writerStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [writerStacks]

/-- The already verified frame emitter is used as a literal finite subroutine. -/
abbrev emit : StructuredCalls.Cmd 4 7 := .call
  (ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram writerRegs writerStacks)

abbrev emitted (d : Data) (bits : List Bool) : Data :=
  ⟨Function.update (Function.update d.regs 0 true) 1 false,
    Function.update (Function.update d.stacks 3 []) 0
      (true :: (Encoding.frame bits ++ d.stacks 0))⟩

theorem emit_eval (d : Data) (bits : List Bool) (hbits : d.stacks 3 = bits.reverse) :
    StructuredCalls.Eval emit (5 * bits.length + 7) d (emitted d bits) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
    (d.stacks 5) (d.stacks 2) (d.stacks 0) bits.reverse
  let b := SubexpNormalizeProgram.filterState true false (d.regs 2)
    (d.stacks 5) (d.stacks 2) (true :: (Encoding.frame bits ++ d.stacks 0)) []
  have ha : embedState writerRegs writerStacks d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ writerRegs_injective writerStacks_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i <;>
        simp [a, writerStacks, SubexpNormalizeProgram.filterState,
          SubexpPostfixControl.quadruple, hbits]
    · intros; rfl
  have hb : embedState writerRegs writerStacks d b = emitted d bits := by
    apply embedState_eq_of_ports _ _ _ _ _ writerRegs_injective writerStacks_injective
    · intro i; fin_cases i <;>
        simp [ writerRegs, b, SubexpNormalizeProgram.filterState,
          SubexpPostfixControl.triple]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      simp [ h0, h1]
    · intro i; fin_cases i <;>
        simp [ writerStacks, b, SubexpNormalizeProgram.filterState,
          SubexpPostfixControl.quadruple]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨2, h.symm⟩
      have h3 : i ≠ 3 := fun h => hi ⟨3, h.symm⟩
      simp [ h0, h3]
  have ht := SubexpNormalizeProgram.emitRecord_trace bits (d.stacks 5) (d.stacks 2)
    (d.stacks 0) (d.regs 0) (d.regs 1) (d.regs 2)
  have h := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram writerRegs writerStacks d
    writerRegs_injective writerStacks_injective ht
  change StructuredCalls.Eval emit (5 * bits.length + 7)
    (embedState writerRegs writerStacks d a) (embedState writerRegs writerStacks d b) at h
  simpa only [ha, hb] using h

/-- Populate singleton pending work and the empty encoded leaf list. -/
abbrev loader : StructuredCalls.Cmd 4 7 :=
  .seq (copy 5 2 4) (.seq (transfer 2 3) (.seq seedLists (.seq emit reset)))

theorem loader_result (regs : Fin 4 → Bool) (bits : List Bool) :
    resetState (emitted (seeded (transferred 2 3 (copied 5 2 (ioState regs [] [] bits [])))) bits) =
      ioState zeroRegs (Encoding.encodeList id [bits]) [false] bits [] := by
  apply data_ext
  · rfl
  · funext i
    fin_cases i <;>
      simp [resetState, ioState, workState,
        stackData, StackRoutines.copyStacks, StackRoutines.transferStacks, Encoding.encodeList]

/-- Measured loading from arbitrary incoming registers; all registers are
cleared before entering the core worklist. -/
theorem loader_eval (regs : Fin 4 → Bool) (bits : List Bool) :
    StructuredCalls.Eval loader (15 * bits.length + 22)
      (ioState regs [] [] bits [])
      (ioState zeroRegs (Encoding.encodeList id [bits]) [false] bits []) := by
  let d := ioState regs [] [] bits []
  have hc := copy_eval 5 2 4 d (by decide) (by decide) (by decide) rfl
  have ht := transfer_eval 2 3 (copied 5 2 d) (by decide)
  have hs := seedLists_eval (transferred 2 3 (copied 5 2 d))
  have hbits : (seeded (transferred 2 3 (copied 5 2 d))).stacks 3 = bits.reverse := by
    simp [ d, workState, stackData,
      StackRoutines.copyStacks, StackRoutines.transferStacks]
  have he := emit_eval (seeded (transferred 2 3 (copied 5 2 d))) bits hbits
  have hr := reset_eval (emitted (seeded (transferred 2 3 (copied 5 2 d))) bits)
  have h := hc.seq (ht.seq (hs.seq (he.seq hr)))
  have htime : (7 * (d.stacks 5).length + 5) +
      ((3 * ((copied 5 2 d).stacks 2).length + 3) + (3 + ((5 * bits.length + 7) + 4))) =
      15 * bits.length + 22 := by
    simp [d, workState, stackData, StackRoutines.copyStacks]
    omega
  rw [htime] at h
  simpa only [d, loader_result] using h

/-- Move encoded leaves forward to their final destination and clear pending. -/
abbrev unloader : StructuredCalls.Cmd 4 7 :=
  .seq (transfer 1 2) (.seq (transfer 2 6) (clear 0))

@[simp] theorem read_zeroRegs : readRegs zeroRegs 0 1 none = zeroRegs := by
  funext i
  fin_cases i <;> simp [zeroRegs, readRegs]

theorem unloader_result (body leaves : List Bool) :
    cleared 0 (transferred 2 6 (transferred 1 2 (ioState zeroRegs [false] leaves body []))) =
      ioState zeroRegs [] [] body leaves := by
  apply data_ext
  · simp [ ioState, workState, read_zeroRegs]
  · funext i
    fin_cases i <;>
      simp [ ioState, workState, stackData, StackRoutines.clearStacks,
        StackRoutines.transferStacks]

/-- Unloading is linear in the raw encoded leaf word; no well-formedness
assumption about the word is needed to preserve its exact forward order. -/
theorem unloader_eval (body leaves : List Bool) :
    StructuredCalls.Eval unloader (6 * leaves.length + 11)
      (ioState zeroRegs [false] leaves body []) (ioState zeroRegs [] [] body leaves) := by
  let d := ioState zeroRegs [false] leaves body []
  have h₁ := transfer_eval 1 2 d (by decide)
  have h₂ := transfer_eval 2 6 (transferred 1 2 d) (by decide)
  have h₃ := clear_eval 0 (transferred 2 6 (transferred 1 2 d))
  have h := h₁.seq (h₂.seq h₃)
  have htime : (3 * (d.stacks 1).length + 3) +
      ((3 * ((transferred 1 2 d).stacks 2).length + 3) +
        (2 * ((transferred 2 6 (transferred 1 2 d)).stacks 0).length + 3)) =
      6 * leaves.length + 11 := by
    simp [d, workState, stackData, StackRoutines.transferStacks]
    omega
  rw [htime] at h
  simpa only [d, unloader_result] using h

def loaderProgram := StructuredCalls.compiled loader (5 : Fin 7) 0
def unloaderProgram := StructuredCalls.compiled unloader (1 : Fin 7) 6

@[simp] theorem loader_size : StructuredCalls.size loader = 36 := by
  simp [ StructuredCalls.size, StructuredProgram.size]

@[simp] theorem unloader_size : StructuredCalls.size unloader = 11 := by
  simp [ StructuredCalls.size]

theorem loader_trace (regs : Fin 4 → Bool) (bits : List Bool) :
    BitProgram.Trace loaderProgram (15 * bits.length + 23)
      ((ioState regs [] [] bits []).withPC (some loaderProgram.entry))
      ((ioState zeroRegs (Encoding.encodeList id [bits]) [false] bits []).withPC none) := by
  simpa [loaderProgram, Nat.add_assoc] using
    StructuredCalls.compiled_halt_trace (loader_eval regs bits) 5 0

theorem unloader_trace (body leaves : List Bool) :
    BitProgram.Trace unloaderProgram (6 * leaves.length + 12)
      ((ioState zeroRegs [false] leaves body []).withPC (some unloaderProgram.entry))
      ((ioState zeroRegs [] [] body leaves).withPC none) := by
  simpa [unloaderProgram, Nat.add_assoc] using
    StructuredCalls.compiled_halt_trace (unloader_eval body leaves) 1 6

theorem loader_primitive (regs : Fin 4 → Bool) (bits : List Bool) :
    Computation.RunsIn (BitProgram.primitive loaderProgram).step
      (BitProgram.primitiveOverhead loaderProgram * (15 * bits.length + 23))
      (BitProgram.primitiveCfg loaderProgram
        ((ioState regs [] [] bits []).withPC (some loaderProgram.entry)))
      (BitProgram.primitiveCfg loaderProgram
        ((ioState zeroRegs (Encoding.encodeList id [bits]) [false] bits []).withPC none)) :=
  BitProgram.primitive_trace _ (loader_trace regs bits)

theorem unloader_primitive (body leaves : List Bool) :
    Computation.RunsIn (BitProgram.primitive unloaderProgram).step
      (BitProgram.primitiveOverhead unloaderProgram * (6 * leaves.length + 12))
      (BitProgram.primitiveCfg unloaderProgram
        ((ioState zeroRegs [false] leaves body []).withPC (some unloaderProgram.entry)))
      (BitProgram.primitiveCfg unloaderProgram
        ((ioState zeroRegs [] [] body leaves).withPC none)) :=
  BitProgram.primitive_trace _ (unloader_trace body leaves)

end SubexponentialSAT.WorklistIOProgram

end OAI.Algorithms

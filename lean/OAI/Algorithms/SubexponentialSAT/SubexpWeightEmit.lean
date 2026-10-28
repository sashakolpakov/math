import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpWeightControl
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-!
# Concrete serialization of a monomial-weight record

The six-stack interface consumes forward index, base, and exponent words on
stacks 0, 1, and 2. It prepends the exact weight-parser record to stack 3.
Stacks 4 and 5 are empty scratch space and are restored. In particular, base
and exponent words are framed in reverse order, as required by the reader.
-/

namespace SubexponentialSAT.SubexpWeightEmit

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 8 6

def regPorts (i : Fin 3) : Fin 8 := ⟨i.val, by omega⟩

theorem regPorts_injective : Function.Injective regPorts := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 8 => k.val) h)

def writerPorts (src : Fin 3) : Fin 4 → Fin 6 := ![4, 5, 3, src.castAdd 3]

theorem writerPorts_injective (src : Fin 3) : Function.Injective (writerPorts src) := by
  fin_cases src <;> decide

abbrev writer (src : Fin 3) : Cmd 8 6 := .call
  (ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram regPorts (writerPorts src))

def finishedRegs (regs : Fin 8 → Bool) : Fin 8 → Bool :=
  Function.update (Function.update regs 0 true) 1 false

def afterWriter (src : Fin 3) (d : Data) (bits : List Bool) : Data :=
  ⟨finishedRegs d.regs, Function.update (Function.update d.stacks (src.castAdd 3) []) 3
    (true :: (Encoding.frame bits ++ d.stacks 3))⟩

theorem writer_eval (src : Fin 3) (d : Data) (bits : List Bool)
    (hs : d.stacks (src.castAdd 3) = bits.reverse) :
    Eval (writer src) (5 * bits.length + 7) d (afterWriter src d bits) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
    (d.stacks 4) (d.stacks 5) (d.stacks 3) bits.reverse
  let b := SubexpNormalizeProgram.filterState true false (d.regs 2)
    (d.stacks 4) (d.stacks 5) (true :: (Encoding.frame bits ++ d.stacks 3)) []
  have ha : embedState regPorts (writerPorts src) d a = d := by
    apply embedState_eq _ _ regPorts_injective (writerPorts_injective src)
    · intro i; fin_cases i <;> rfl
    · intro i
      fin_cases i <;> simp [a, writerPorts, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple, hs]
    · intros; rfl
    · intros; rfl
  have hb : embedState regPorts (writerPorts src) d b = afterWriter src d bits := by
    apply embedState_eq _ _ regPorts_injective (writerPorts_injective src)
    · intro i
      fin_cases i <;> simp [afterWriter, finishedRegs, regPorts, b,
        SubexpNormalizeProgram.filterState, SubexpPostfixControl.triple]
    · intro i
      fin_cases src <;> fin_cases i <;> simp [afterWriter, writerPorts, b,
        SubexpNormalizeProgram.filterState, SubexpPostfixControl.quadruple]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      simp [afterWriter, finishedRegs, h0, h1]
    · intro i hi
      have hs' : i ≠ src.castAdd 3 := fun h => hi ⟨3, h.symm⟩
      have ho : i ≠ 3 := fun h => hi ⟨2, h.symm⟩
      simp [afterWriter, hs', ho]
  have ht := SubexpNormalizeProgram.emitRecord_trace bits (d.stacks 4) (d.stacks 5)
    (d.stacks 3) (d.regs 0) (d.regs 1) (d.regs 2)
  have h := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram regPorts
    (writerPorts src) d regPorts_injective (writerPorts_injective src) ht
  change Eval _ _ (embedState _ _ d a) (embedState _ _ d b) at h
  simpa only [writer, ha, hb] using h

abbrev pop : Cmd 8 6 := .base (.atom (.pop 3 0 1))

def state (regs : Fin 8 → Bool) (index base exponent output : List Bool) : Data :=
  ⟨regs, ![index, base, exponent, output, [], []]⟩

theorem writer_exponent (regs : Fin 8 → Bool) (index base exponent output : List Bool) :
    Eval (writer 2) (5 * exponent.length + 7)
      (state regs index base exponent output)
      (state (finishedRegs regs) index base []
        (true :: (Encoding.frame exponent.reverse ++ output))) := by
  have h := writer_eval 2 (state regs index base exponent output) exponent.reverse
    (by simp [state])
  have he : afterWriter 2 (state regs index base exponent output) exponent.reverse =
      state (finishedRegs regs) index base []
        (true :: (Encoding.frame exponent.reverse ++ output)) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext j; fin_cases j <;> rfl
  simpa only [he, List.length_reverse] using h

theorem writer_base (regs : Fin 8 → Bool) (index base exponent output : List Bool) :
    Eval (writer 1) (5 * base.length + 7)
      (state regs index base exponent output)
      (state (finishedRegs regs) index [] exponent
        (true :: (Encoding.frame base.reverse ++ output))) := by
  have h := writer_eval 1 (state regs index base exponent output) base.reverse
    (by simp [state])
  have he : afterWriter 1 (state regs index base exponent output) base.reverse =
      state (finishedRegs regs) index [] exponent
        (true :: (Encoding.frame base.reverse ++ output)) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext j; fin_cases j <;> rfl
  simpa only [he, List.length_reverse] using h

theorem writer_index (regs : Fin 8 → Bool) (index base exponent output : List Bool) :
    Eval (writer 0) (5 * index.length + 7)
      (state regs index.reverse base exponent output)
      (state (finishedRegs regs) [] base exponent
        (true :: (Encoding.frame index ++ output))) := by
  have h := writer_eval 0 (state regs index.reverse base exponent output) index rfl
  have he : afterWriter 0 (state regs index.reverse base exponent output) index =
      state (finishedRegs regs) [] base exponent
        (true :: (Encoding.frame index ++ output)) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext j; fin_cases j <;> rfl
  simpa only [he] using h

theorem pop_eval (regs : Fin 8 → Bool) (index base exponent output : List Bool) :
    Eval pop 1 (state regs index base exponent (true :: output))
      (state (readRegs regs 0 1 (some true)) index base exponent output) := by
  apply Eval.base
  have h := StructuredProgram.Eval.atom (.pop (3 : Fin 6) (0 : Fin 8) 1)
    (state regs index base exponent (true :: output))
  have hs : Function.update (![index, base, exponent, true :: output, [], []] : Fin 6 → List Bool)
      3 output = ![index, base, exponent, output, [], []] := by
    funext j; fin_cases j <;> rfl
  simpa [pop, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, state, hs] using h

abbrev reverseIndex : Cmd 8 6 := .call (StackRoutines.reverseProgram 0 4 5 0 1)

theorem reverseIndex_eval (regs : Fin 8 → Bool) (index base exponent output : List Bool) :
    Eval reverseIndex (9 * index.length + 7) (state regs index base exponent output)
      (state (readRegs regs 0 1 none) index.reverse base exponent output) := by
  have h := reverse_eval (state regs index base exponent output) 0 4 5 0 1
    (by decide) (by decide) (by decide) (by decide) rfl rfl
  have he : afterReverse (state regs index base exponent output) 0 0 1 =
      state (readRegs regs 0 1 none) index.reverse base exponent output := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext j; fin_cases j <;> rfl
  have hl : (state regs index base exponent output).stacks 0 = index := rfl
  simpa only [reverseIndex, he, hl] using h

abbrev command : Cmd 8 6 :=
  .seq (writer 2) (.seq pop (.seq (writer 1) (.seq pop (.seq reverseIndex (writer 0)))))

abbrev program : Program 8 6 (size command + 1) := compiled command 0 3

theorem program_labels : size command + 1 = 64 := by rfl

def recordBits (index base exponent : List Bool) : List Bool :=
  true :: (Encoding.frame index ++ Encoding.frame base.reverse ++ Encoding.frame exponent.reverse)

theorem recordBits_payload (r : SubexpWeightControl.WeightRecord) :
    recordBits r.index r.base r.exponent = true :: SubexpWeightControl.payload r := rfl

theorem command_eval (regs : Fin 8 → Bool) (index base exponent output : List Bool) :
    Eval command (14 * index.length + 5 * base.length + 5 * exponent.length + 30)
      (state regs index base exponent output)
      (state (finishedRegs regs) [] [] [] (recordBits index base exponent ++ output)) := by
  let re := finishedRegs regs
  let rp := readRegs re 0 1 (some true)
  let rb := finishedRegs rp
  let rq := readRegs rb 0 1 (some true)
  let rr := readRegs rq 0 1 none
  let oe := Encoding.frame exponent.reverse ++ output
  let ob := Encoding.frame base.reverse ++ oe
  have he := writer_exponent regs index base exponent output
  have hp := pop_eval re index base [] oe
  have hb := writer_base rp index base [] oe
  have hq := pop_eval rb index [] [] ob
  have hr := reverseIndex_eval rq index [] [] ob
  have hi := writer_index rr index [] [] ob
  have h := Eval.seq he (Eval.seq hp (Eval.seq hb (Eval.seq hq (Eval.seq hr hi))))
  have hregs : finishedRegs rr = finishedRegs regs := by
    funext j
    fin_cases j <;> simp [rr, rq, rb, rp, re, finishedRegs, readRegs]
  have hcost : 5 * exponent.length + 7 + (1 + (5 * base.length + 7 +
      (1 + (9 * index.length + 7 + (5 * index.length + 7))))) =
      14 * index.length + 5 * base.length + 5 * exponent.length + 30 := by omega
  simpa only [command, hcost, hregs, recordBits, List.cons_append, List.append_assoc, ob, oe] using h

theorem program_trace (regs : Fin 8 → Bool) (index base exponent output : List Bool) :
    Trace program (14 * index.length + 5 * base.length + 5 * exponent.length + 31)
      ((state regs index base exponent output).withPC (some program.entry))
      ((state (finishedRegs regs) [] [] []
        (recordBits index base exponent ++ output)).withPC none) := by
  simpa only [Nat.add_assoc] using compiled_halt_trace
    (command_eval regs index base exponent output) 0 3

/-- This is the exact cons operation on the input representation consumed by
the weight program, including preservation of an arbitrary trailing suffix. -/
theorem program_record_trace (regs : Fin 8 → Bool)
    (r : SubexpWeightControl.WeightRecord) (rest : List SubexpWeightControl.WeightRecord)
    (suffix : List Bool) :
    Trace program (14 * r.index.length + 5 * r.base.length + 5 * r.exponent.length + 31)
      ((state regs r.index r.base r.exponent
        (SubexpWeightControl.encodeRecords rest ++ suffix)).withPC (some program.entry))
      ((state (finishedRegs regs) [] [] []
        (SubexpWeightControl.encodeRecords (r :: rest) ++ suffix)).withPC none) := by
  simpa only [recordBits_payload, SubexpWeightControl.encodeRecords,
    List.cons_append, List.append_assoc] using
    program_trace regs r.index r.base r.exponent (SubexpWeightControl.encodeRecords rest ++ suffix)

theorem recordBits_length (index base exponent : List Bool) :
    (recordBits index base exponent).length =
      2 * (index.length + base.length + exponent.length) + 4 := by
  simp only [recordBits, List.length_cons, List.length_append, Encoding.length_frame,
    List.length_reverse]
  omega

theorem program_primitive (regs : Fin 8 → Bool) (index base exponent output : List Bool) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program *
        (14 * index.length + 5 * base.length + 5 * exponent.length + 31))
      (primitiveCfg program ((state regs index base exponent output).withPC (some program.entry)))
      (primitiveCfg program ((state (finishedRegs regs) [] [] []
        (recordBits index base exponent ++ output)).withPC none)) :=
  primitive_trace program (program_trace regs index base exponent output)

end SubexponentialSAT.SubexpWeightEmit

end OAI.Algorithms

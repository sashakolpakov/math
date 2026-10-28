import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LagrangePacketProgram
import OAI.Algorithms.SubexponentialSAT.CounterConversions

namespace OAI.Algorithms

/-! The table generator emits little-endian binary labels. This fixed
composition converts one label to unary and immediately runs the actual
cache selector; no decoded numeric label is a machine instruction. -/

namespace SubexponentialSAT.Subexp.LagrangePacketBinary

open BitProgram StructuredCalls LagrangePacketProgram

def counterPorts : Fin 3 → Fin 12 := ![0, 2, 4]

theorem counterPorts_injective : Function.Injective counterPorts := by decide

def convertedRegs (regs : Fin 8 → Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update regs 0 false) 1 false) 2 false

abbrev convertLabel : Cmd 8 12 :=
  .call (ProgramLinking.liftProgram CounterConversions.unaryProgram smallRegs counterPorts)

theorem convertLabel_eval (regs : Fin 8 → Bool) (bits cache saved acc : Word) :
    ∃ n ≤ CounterConversions.runtimeBound bits,
      Eval convertLabel n
        (state regs bits [] [] cache [] saved acc)
        (state (convertedRegs regs) [] []
          (List.replicate (CounterPrograms.value bits) true) cache [] saved acc) := by
  let a := state regs bits [] [] cache [] saved acc
  let b := state (convertedRegs regs) [] []
    (List.replicate (CounterPrograms.value bits) true) cache [] saved acc
  let x := CounterConversions.state (fun j => regs (smallRegs j)) bits []
  let y := CounterConversions.state CounterConversions.zeroRegs []
    (List.replicate (CounterPrograms.value bits) true)
  obtain ⟨n, hn, ht⟩ := CounterConversions.unary_runs (fun j => regs (smallRegs j)) bits []
  have hx : embedState smallRegs counterPorts a x = a := by
    apply SelectorMapProgram.embed_eq _ _ smallRegs_injective counterPorts_injective
    · intro j; rfl
    · intro j; fin_cases j <;> rfl
    · intros; rfl
    · intros; rfl
  have hy : embedState smallRegs counterPorts a y = b := by
    apply SelectorMapProgram.embed_eq _ _ smallRegs_injective counterPorts_injective
    · intro j; fin_cases j <;> rfl
    · intro j; fin_cases j <;> rfl
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      have h2 : j ≠ 2 := fun h => hj ⟨2, h.symm⟩
      simp [a, b, state, convertedRegs, h0, h1, h2]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
      have h2 : j ≠ 2 := fun h => hj ⟨1, h.symm⟩
      have h4 : j ≠ 4 := fun h => hj ⟨2, h.symm⟩
      fin_cases j <;> simp_all [a, b, state]
  have ht' : Trace CounterConversions.unaryProgram n
      (x.withPC (some CounterConversions.unaryProgram.entry)) (y.withPC none) := by
    simpa only [x, y, List.append_nil] using ht
  have he := eval_call_lifted CounterConversions.unaryProgram smallRegs counterPorts a
    smallRegs_injective counterPorts_injective ht'
  exact ⟨n, hn, by simpa only [convertLabel, hx, hy, a, b] using he⟩

abbrev command : Cmd 8 12 := .seq convertLabel (.call LagrangePacketProgram.program)
def program := compiled command 0 11

def cost (before : List Word) (coefficients : Word) (after : List Word)
    (saved bits : Word) : ℕ :=
  CounterConversions.runtimeBound bits +
    LagrangePacketProgram.cost before coefficients after saved + 1

/-- The original binary label, its physical conversion, the cache scan, and
the output framing are all part of one fixed program. -/
theorem program_runsIn (before : List Word) (coefficients : Word) (after : List Word)
    (saved bits acc : Word) (hi : CounterPrograms.value bits = before.length)
    (regs : Fin 8 → Bool) :
    ∃ rf, RunsIn program (cost before coefficients after saved bits)
      ((state regs bits [] []
        (ProgramEncoding.encodeRecords (before ++ coefficients :: after)) [] saved.reverse acc).withPC
          (some program.entry))
      ((state rf [] [] []
        (ProgramEncoding.encodeRecords (before ++ coefficients :: after)) [] []
        (TupleProgram.prependRecord (SelectorPairProgram.payload saved coefficients) acc)).withPC none) := by
  let cache := ProgramEncoding.encodeRecords (before ++ coefficients :: after)
  obtain ⟨n, hn, hc⟩ := convertLabel_eval regs bits cache saved.reverse acc
  obtain ⟨rf, hp⟩ := LagrangePacketProgram.program_trace before coefficients after
    saved (List.replicate (CounterPrograms.value bits) true) acc
    (by simpa only [List.length_replicate] using hi) (convertedRegs regs)
  have hall := hc.seq (Eval.call _ hp)
  refine ⟨rf, n + LagrangePacketProgram.cost before coefficients after saved + 1, ?_, ?_⟩
  · unfold cost
    omega
  · exact compiled_halt_trace hall 0 11

theorem program_primitive (before : List Word) (coefficients : Word) (after : List Word)
    (saved bits acc : Word) (hi : CounterPrograms.value bits = before.length)
    (regs : Fin 8 → Bool) :
    ∃ rf, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * cost before coefficients after saved bits)
      (BitProgram.primitiveCfg program
        ((state regs bits [] []
          (ProgramEncoding.encodeRecords (before ++ coefficients :: after)) [] saved.reverse acc).withPC
            (some program.entry)))
      (BitProgram.primitiveCfg program
        ((state rf [] [] []
          (ProgramEncoding.encodeRecords (before ++ coefficients :: after)) [] []
          (TupleProgram.prependRecord (SelectorPairProgram.payload saved coefficients) acc)).withPC none)) := by
  obtain ⟨rf, h⟩ := program_runsIn before coefficients after saved bits acc hi regs
  exact ⟨rf, BitProgram.primitive_execution program h⟩

end SubexponentialSAT.Subexp.LagrangePacketBinary

end OAI.Algorithms

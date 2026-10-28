import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpChunkDescriptorOutput
import OAI.Algorithms.SubexponentialSAT.SubexpChunkDescriptorInput

namespace OAI.Algorithms

/-!
# Binary-input chunk descriptors from one fixed finite program

Input stacks 0 and 1 hold little-endian binary n and ell. All other stacks
start empty. Output 8 contains framed unary chunk widths; output 9 contains
the matching framed singleton scopes. The positive-ell premise ensures that
every nonempty chunk iteration consumes input.
-/

namespace SubexponentialSAT.SubexpChunkDescriptor

open BitProgram StructuredProgram StructuredCalls
open SubexpChunkDescriptorProgram SubexpChunkDescriptorEncoding

abbrev command : StructuredCalls.Cmd 3 10 :=
  .seq SubexpChunkDescriptorInput.command SubexpChunkDescriptorOutput.unaryCmd

def initialState (regs : Regs) (nBits ellBits : List Bool) : Data :=
  work regs nBits ellBits [] [] [] []

def finalState (regs : Regs) (n ell : ℕ) : Data :=
  SubexpChunkDescriptorOutput.outputState regs (List.replicate ell true)
    (List.replicate (ChunkPartition.count n ell) true)
    (widthShapes n ell) (scopes 0 (ChunkPartition.count n ell))

def runtimeBound (nBits ellBits : List Bool) : ℕ :=
  SubexpChunkDescriptorInput.runtimeBound nBits ellBits +
    SubexpChunkDescriptorOutput.unaryBound
      (CounterPrograms.value nBits) (CounterPrograms.value ellBits)

theorem execution (regs : Regs) (nBits ellBits : List Bool)
    (hell : 0 < CounterPrograms.value ellBits) :
    ∃ steps regs', StructuredCalls.Eval command steps (initialState regs nBits ellBits)
      (finalState regs' (CounterPrograms.value nBits) (CounterPrograms.value ellBits)) ∧
      steps ≤ runtimeBound nBits ellBits := by
  obtain ⟨ni, ri, hi, hni⟩ := SubexpChunkDescriptorInput.input_execution regs nBits ellBits
  obtain ⟨no, ro, ho, hno⟩ := SubexpChunkDescriptorOutput.unary_execution ri
    (List.replicate (CounterPrograms.value nBits) true)
    (List.replicate (CounterPrograms.value ellBits) true) (by simpa using hell)
  refine ⟨ni + no, ro, ?_, ?_⟩
  · simpa [command, initialState, finalState] using hi.seq ho
  · simpa [runtimeBound] using Nat.add_le_add hni hno

def program := StructuredCalls.compiled command (0 : Fin 10) 8

theorem runs (regs : Regs) (nBits ellBits : List Bool)
    (hell : 0 < CounterPrograms.value ellBits) :
    ∃ regs', BitProgram.RunsIn program (runtimeBound nBits ellBits + 1)
      ((initialState regs nBits ellBits).withPC (some program.entry))
      ((finalState regs' (CounterPrograms.value nBits) (CounterPrograms.value ellBits)).withPC none) := by
  obtain ⟨n, regs', he, hn⟩ := execution regs nBits ellBits hell
  exact ⟨regs', n + 1, by omega, StructuredCalls.compiled_halt_trace he 0 8⟩

theorem polynomial_runs (regs : Regs) (nBits ellBits : List Bool)
    (hell : 0 < CounterPrograms.value ellBits) :
    ∃ regs', BitProgram.RunsIn program
      (SubexpChunkDescriptorInput.runtimeBound nBits ellBits +
        200 * (CounterPrograms.value nBits + CounterPrograms.value ellBits + 1) ^ 2 + 1)
      ((initialState regs nBits ellBits).withPC (some program.entry))
      ((finalState regs' (CounterPrograms.value nBits) (CounterPrograms.value ellBits)).withPC none) := by
  obtain ⟨regs', n, hn, he⟩ := runs regs nBits ellBits hell
  refine ⟨regs', n, ?_, he⟩
  have hb := SubexpChunkDescriptorOutput.unaryBound_polynomial
    (CounterPrograms.value nBits) (CounterPrograms.value ellBits) hell
  dsimp [runtimeBound] at hn
  omega

theorem primitive_runs (regs : Regs) (nBits ellBits : List Bool)
    (hell : 0 < CounterPrograms.value ellBits) :
    ∃ regs', Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * (runtimeBound nBits ellBits + 1))
      (BitProgram.primitiveCfg program ((initialState regs nBits ellBits).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((finalState regs' (CounterPrograms.value nBits) (CounterPrograms.value ellBits)).withPC none)) := by
  obtain ⟨regs', he⟩ := runs regs nBits ellBits hell
  exact ⟨regs', BitProgram.primitive_execution program he⟩

theorem lifted_execution {R S : ℕ} (register : Fin 3 → Fin R) (stack : Fin 10 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (frame : StructuredProgram.State R S) (regs : Regs) (nBits ellBits : List Bool)
    (hell : 0 < CounterPrograms.value ellBits) :
    ∃ steps regs', StructuredCalls.Eval (.call (ProgramLinking.liftProgram program register stack))
      steps (StructuredCalls.embedState register stack frame (initialState regs nBits ellBits))
      (StructuredCalls.embedState register stack frame
        (finalState regs' (CounterPrograms.value nBits) (CounterPrograms.value ellBits))) ∧
      steps ≤ runtimeBound nBits ellBits + 1 := by
  obtain ⟨regs', n, hn, he⟩ := runs regs nBits ellBits hell
  exact ⟨n, regs', StructuredCalls.eval_call_lifted program register stack frame
    hregister hstack he, hn⟩

@[simp] theorem final_widths (regs : Regs) (n ell : ℕ) :
    (finalState regs n ell).stacks 8 =
      Encoding.encodeList id ((widths n ell).map (fun b => List.replicate b true)) := rfl

@[simp] theorem final_scopes (regs : Regs) (n ell : ℕ) :
    (finalState regs n ell).stacks 9 = Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
      ((List.range (ChunkPartition.count n ell)).map List.singleton) := by
  rw [List.range_eq_range']
  rfl

theorem aligned (n ell : ℕ) :
    ((widths n ell).map (fun b => List.replicate b true)).length =
      ((List.range (ChunkPartition.count n ell)).map List.singleton).length := by
  simp

theorem final_lengths (regs : Regs) (n ell : ℕ) (hell : 0 < ell) :
    ((finalState regs n ell).stacks 8).length = 2 * n + 2 * ChunkPartition.count n ell + 1 ∧
      ((finalState regs n ell).stacks 9).length =
        ChunkPartition.count n ell * (2 * ChunkPartition.count n ell + 10) + 1 :=
  SubexpChunkDescriptorOutput.descriptor_lengths n ell hell

theorem final_word_bound (regs : Regs) (n ell : ℕ) (hell : 0 < ell) (i : Fin 10) :
    ((finalState regs n ell).stacks i).length ≤ 16 * (n + ell + 1) ^ 2 := by
  have hD : ChunkPartition.count n ell ≤ n := by
    apply (ChunkPartition.count_le_iff hell).mpr
    exact Nat.le_mul_of_pos_right n hell
  have hsq := Nat.mul_self_le_mul_self hD
  obtain ⟨hwidth, hscope⟩ := final_lengths regs n ell hell
  fin_cases i <;>
    simp [finalState, SubexpChunkDescriptorOutput.outputState] at *
  all_goals nlinarith [Nat.zero_le (n * ell)]

end SubexponentialSAT.SubexpChunkDescriptor

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpChunkDescriptorLoop

namespace OAI.Algorithms

/-! Terminate and reverse the two actual descriptor accumulators. -/

namespace SubexponentialSAT.SubexpChunkDescriptorOutput

open BitProgram StructuredProgram StructuredCalls
open SubexpChunkDescriptorProgram SubexpChunkDescriptorEncoding SubexpChunkDescriptorLoop

abbrev transfer (src dst : Fin 10) : StructuredCalls.Cmd 3 10 :=
  .call (StackRoutines.transferProgram src dst 0 1)

def transferred (src dst : Fin 10) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

theorem transfer_eval (src dst : Fin 10) (h : src ≠ dst) (d : Data) :
    StructuredCalls.Eval (transfer src dst) (3 * (d.stacks src).length + 3) d
      (transferred src dst d) :=
  .call _ (ListRegisterProgram.transfer_run src dst 0 1 h (by decide) d.regs d.stacks)

def outputState (regs : Regs) (width index widthStream scopeStream : List Bool) : Data :=
  ⟨regs, ![[], width, [], [], index, [], [], [], widthStream, scopeStream]⟩

abbrev finish : StructuredCalls.Cmd 3 10 :=
  .seq (emitBits 5 [false]) (.seq (emitBits 6 [false]) (.seq (transfer 5 8) (transfer 6 9)))

theorem finish_eval (regs : Regs) (width index ws ss : List Bool) :
    ∃ regs', StructuredCalls.Eval finish (3 * (ws.length + ss.length) + 16)
      (work regs [] width [] index ws ss)
      (outputState regs' width index (ws.reverse ++ [false]) (ss.reverse ++ [false])) := by
  obtain ⟨r₁, h₁⟩ := emitBits_work5 [false] regs [] width [] index ws ss
  obtain ⟨r₂, h₂⟩ := emitBits_work6 [false] r₁ [] width [] index (false :: ws) ss
  let d := work r₂ [] width [] index (false :: ws) (false :: ss)
  have h₃ := transfer_eval 5 8 (by decide) d
  have h₄ := transfer_eval 6 9 (by decide) (transferred 5 8 d)
  refine ⟨(transferred 6 9 (transferred 5 8 d)).regs, ?_⟩
  have he := h₁.seq (h₂.seq (h₃.seq h₄))
  convert he using 1
  · simp [d, work, transferred, StackRoutines.transferStacks]
    omega
  · apply CounterForPrograms.data_ext
    · rfl
    · funext i
      fin_cases i <;> simp [outputState, d, work, transferred, StackRoutines.transferStacks]

abbrev unaryCmd : StructuredCalls.Cmd 3 10 := .seq scan finish

def unaryBound (n ell : ℕ) : ℕ :=
  loopBound ell 0 (ChunkPartition.count n ell) + 17 +
    3 * ((widthPrefix n ell).length + (scopePrefix 0 (ChunkPartition.count n ell)).length)

theorem unary_execution (regs : Regs) (remaining width : List Bool) (hw : 0 < width.length) :
    ∃ steps regs', StructuredCalls.Eval unaryCmd steps (work regs remaining width [] [] [] [])
      (outputState regs' width (List.replicate (ChunkPartition.count remaining.length width.length) true)
        (widthShapes remaining.length width.length)
        (scopes 0 (ChunkPartition.count remaining.length width.length))) ∧
      steps ≤ unaryBound remaining.length width.length := by
  obtain ⟨n, r₁, h₁, hn⟩ := scan_eval regs remaining width hw
  obtain ⟨r₂, h₂⟩ := finish_eval r₁ width
    (List.replicate (ChunkPartition.count remaining.length width.length) true)
    (widthPrefix remaining.length width.length).reverse
    (scopePrefix 0 (ChunkPartition.count remaining.length width.length)).reverse
  refine ⟨n + (3 * ((widthPrefix remaining.length width.length).reverse.length +
      (scopePrefix 0 (ChunkPartition.count remaining.length width.length)).reverse.length) + 16),
    r₂, ?_, ?_⟩
  · simpa [unaryCmd, widthShapes_eq, scopes_eq] using h₁.seq h₂
  · simp only [List.length_reverse]
    dsimp [unaryBound]
    omega

def unaryProgram := StructuredCalls.compiled unaryCmd (0 : Fin 10) 8

theorem unary_runs (regs : Regs) (remaining width : List Bool) (hw : 0 < width.length) :
    ∃ regs', BitProgram.RunsIn unaryProgram (unaryBound remaining.length width.length + 1)
      ((work regs remaining width [] [] [] []).withPC (some unaryProgram.entry))
      ((outputState regs' width (List.replicate (ChunkPartition.count remaining.length width.length) true)
        (widthShapes remaining.length width.length)
        (scopes 0 (ChunkPartition.count remaining.length width.length))).withPC none) := by
  obtain ⟨n, regs', he, hn⟩ := unary_execution regs remaining width hw
  exact ⟨regs', n + 1, by omega, StructuredCalls.compiled_halt_trace he 0 8⟩

theorem unary_primitive (regs : Regs) (remaining width : List Bool) (hw : 0 < width.length) :
    ∃ regs', Computation.RunsIn (BitProgram.primitive unaryProgram).step
      (BitProgram.primitiveOverhead unaryProgram * (unaryBound remaining.length width.length + 1))
      (BitProgram.primitiveCfg unaryProgram
        ((work regs remaining width [] [] [] []).withPC (some unaryProgram.entry)))
      (BitProgram.primitiveCfg unaryProgram
        ((outputState regs' width (List.replicate (ChunkPartition.count remaining.length width.length) true)
          (widthShapes remaining.length width.length)
          (scopes 0 (ChunkPartition.count remaining.length width.length))).withPC none)) := by
  obtain ⟨regs', he⟩ := unary_runs regs remaining width hw
  exact ⟨regs', BitProgram.primitive_execution unaryProgram he⟩

theorem widthPrefix_length (n ell : ℕ) (hell : 0 < ell) :
    (widthPrefix n ell).length = 2 * n + 2 * ChunkPartition.count n ell := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simp [widthPrefix_zero hell, ChunkPartition.count_zero hell]
      · have hp : 0 < n := by omega
        rw [widthPrefix_step hp hell, List.length_append, width_record]
        simp only [List.length_append, List.length_singleton, List.length_replicate]
        rw [ih (n - ell) (by omega), count_step hp hell]
        omega

theorem scopePrefix_length (start count : ℕ) :
    (scopePrefix start count).length = count * (4 * start + 2 * count + 10) := by
  induction count generalizing start with
  | zero => simp
  | succ count ih =>
      rw [scopePrefix_step, List.length_append, scope_record]
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
      rw [ih]
      dsimp [scopeSuffix]
      ring

theorem descriptor_lengths (n ell : ℕ) (hell : 0 < ell) :
    (widthShapes n ell).length = 2 * n + 2 * ChunkPartition.count n ell + 1 ∧
      (scopes 0 (ChunkPartition.count n ell)).length =
        ChunkPartition.count n ell * (2 * ChunkPartition.count n ell + 10) + 1 := by
  simp [widthShapes_eq, scopes_eq, widthPrefix_length n ell hell, scopePrefix_length]

theorem unaryBound_polynomial (n ell : ℕ) (hell : 0 < ell) :
    unaryBound n ell ≤ 200 * (n + ell + 1) ^ 2 := by
  have hD : ChunkPartition.count n ell ≤ n := by
    apply (ChunkPartition.count_le_iff hell).mpr
    exact Nat.le_mul_of_pos_right n hell
  have hmul := Nat.mul_le_mul_right ell hD
  have hsq := Nat.mul_self_le_mul_self hD
  simp only [unaryBound, loopBound, widthPrefix_length n ell hell, scopePrefix_length,
    Nat.zero_add, Nat.mul_zero ]
  nlinarith [Nat.zero_le (n * ell)]

end SubexponentialSAT.SubexpChunkDescriptorOutput

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchExecution
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCoefficientProgram

namespace OAI.Algorithms

/-! A fixed executable prime-field kernel-basis and complement search. -/

namespace SubexponentialSAT.Subexp.BlockSearchConcrete

open BitProgram StructuredCalls BlockSearch BlockSearchEncoding BlockSearchPredicate
open SubexpTupleRefinement

/-- This instruction table is independent of the prime and matrix dimensions. -/
def program := BlockSearchExecution.program BlockCoefficientProgram.matrixPair

def inputState (p : ℕ) [Fact p.Prime] {m N : ℕ}
    (M : Fin m → Fin N → ZMod p) (regs : Fin 24 → Bool) : StructuredProgram.State 24 42 :=
  BlockSearchExecution.inputState (BlockCoefficientProgram.context p M) (scalarCode p)
    (QuarticSearch.elements p) N regs

def cost (p : ℕ) [Fact p.Prime] (m N : ℕ) : ℕ :=
  BlockSearchExecution.cost (scalarCode p) (QuarticSearch.elements p) N
    (BlockCoefficientProgram.coefficientCost p m N)

/-- The complete instruction bound is exponential in a polynomial of the
local dimension and logarithmic field width, including tuple generation. -/
theorem cost_le (p : ℕ) [Fact p.Prime] (m N : ℕ) :
    cost p m N ≤
      800 * (N * N + 1) * p ^ (N * N) *
        ((N * N + 1) * (2 * MatrixWordEncoding.width p + 1) + 1) +
      800 * (N + 1) * p ^ N * ((N + 1) * (2 * MatrixWordEncoding.width p + 1) + 1) +
      6 * N ^ 2 + 22 * N + 37 +
      BlockSearchExecution.searchBound p N (2 * MatrixWordEncoding.width p + 1)
        (BlockCoefficientProgram.coefficientCost p m N) := by
  have hp := (show Nat.Prime p from Fact.out).two_le
  have ha : 1 ≤ (QuarticSearch.elements p).length := by
    rw [QuarticSearch.length_elements]
    omega
  have h := BlockSearchBounds.cost_le (scalarCode p) (QuarticSearch.elements p) ha N
    (BlockCoefficientProgram.coefficientCost p m N)
  simpa only [cost, QuarticSearch.length_elements, scalarCode,
    BlockSearchProgram.framedCode, MatrixWordEncoding.code] using h

theorem validCoefficient_eq (p : ℕ) [Fact p.Prime] (N : ℕ) :
    BlockSearchCoverage.ValidCoefficient (scalarCode p) N =
      BlockCoefficientProgram.validCoefficient p N := by
  funext bits
  apply propext
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa only [encoded_vector_eq_words, BlockCoefficientProgram.vectorWords] using hx
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa only [encoded_vector_eq_words, BlockCoefficientProgram.vectorWords] using hx

theorem tableBits_eq (p : ℕ) [Fact p.Prime] {N : ℕ}
    (C : Fin N → Fin N → ZMod p) :
    encodeTuple (scalarCode p) (flattenTable C) = BlockCoefficientProgram.tableBits p C := by
  simpa only [BlockCoefficientProgram.tableBits, BlockCoefficientProgram.matrixBits,
    BlockCoefficientProgram.matrixRows, BlockCoefficientProgram.vectorWords] using
      encoded_table_eq_flatten_words p C

theorem coefficientContract_with_alphabet (p : ℕ) [Fact p.Prime]
    (alphabet : List (ZMod p)) (hfull : ∀ x, x ∈ alphabet) {m N : ℕ}
    (M : Fin m → Fin N → ZMod p) (C : Fin N → Fin N → ZMod p) (d : Fin (N + 1)) :
    BlockSearchLoop.CoefficientContract BlockCoefficientProgram.matrixPair
      (BlockCoefficientProgram.context p M) (encodeTuple (scalarCode p) (flattenTable C))
      (splitCode d)
      (encodedTest (scalarCode p) alphabet M
        (encodeTuple (scalarCode p) (flattenTable C)) (splitCode d))
      (fun _ => BlockCoefficientProgram.coefficientCost p m N)
      (BlockSearchCoverage.ValidCoefficient (scalarCode p) N) := by
  have hc := BlockCoefficientProgram.coefficientContract p M C d
    (encodedTest (scalarCode p) alphabet M
      (encodeTuple (scalarCode p) (flattenTable C)) (splitCode d)) (fun x => by
        simpa only [test, BlockCoefficientProgram.vectorWords] using
          test_on_words p alphabet hfull M d C x)
  simpa only [← tableBits_eq p C, ← validCoefficient_eq p N, splitCode] using hc

theorem coefficientContract (p : ℕ) [Fact p.Prime] {m N : ℕ}
    (M : Fin m → Fin N → ZMod p) (C : Fin N → Fin N → ZMod p) (d : Fin (N + 1)) :
    BlockSearchLoop.CoefficientContract BlockCoefficientProgram.matrixPair
      (BlockCoefficientProgram.context p M) (encodeTuple (scalarCode p) (flattenTable C))
      (splitCode d)
      (encodedTest (scalarCode p) (QuarticSearch.elements p) M
        (encodeTuple (scalarCode p) (flattenTable C)) (splitCode d))
      (fun _ => BlockCoefficientProgram.coefficientCost p m N)
      (BlockSearchCoverage.ValidCoefficient (scalarCode p) N) :=
  coefficientContract_with_alphabet p (QuarticSearch.elements p)
    (QuarticSearch.mem_elements p) M C d

/-- The executable search accepts any supplied complete scalar alphabet,
including the reversed order emitted by the scalar-alphabet formatter. -/
theorem program_runsIn_with_alphabet (p : ℕ) [Fact p.Prime]
    (alphabet : List (ZMod p)) (hfull : ∀ x, x ∈ alphabet) {m N : ℕ}
    (M : Fin m → Fin N → ZMod p) (regs : Fin 24 → Bool) :
    ∃ (next : StructuredProgram.State 24 42) (C : Fin N → Fin N → ZMod p) (d : Fin (N + 1)),
      GoodPair M (splitPair d C) ∧ next.stacks 41 = encodeTuple (scalarCode p) (flattenTable C) ∧
      next.stacks 8 = splitCode d ∧
      RunsIn program
        (BlockSearchExecution.cost (scalarCode p) alphabet N
          (BlockCoefficientProgram.coefficientCost p m N))
        ((BlockSearchExecution.inputState (BlockCoefficientProgram.context p M)
          (scalarCode p) alphabet N regs).withPC (some program.entry)) (next.withPC none) :=
  BlockSearchExecution.program_runsIn BlockCoefficientProgram.matrixPair
    (BlockCoefficientProgram.context p M) (scalarCode p) alphabet hfull M
    (BlockCoefficientProgram.coefficientCost p m N) rfl
    (coefficientContract_with_alphabet p alphabet hfull M) regs

/-- All enumeration, arithmetic tests, and selection are executions of the
same fixed instruction table. The output supplies a certified kernel basis
and complement for the input matrix. -/
theorem program_runsIn (p : ℕ) [Fact p.Prime] {m N : ℕ}
    (M : Fin m → Fin N → ZMod p) (regs : Fin 24 → Bool) :
    ∃ (next : StructuredProgram.State 24 42) (C : Fin N → Fin N → ZMod p) (d : Fin (N + 1)),
      GoodPair M (splitPair d C) ∧ next.stacks 41 = encodeTuple (scalarCode p) (flattenTable C) ∧
      next.stacks 8 = splitCode d ∧
      RunsIn program (cost p m N)
        ((inputState p M regs).withPC (some program.entry)) (next.withPC none) := by
  exact BlockSearchExecution.program_runsIn BlockCoefficientProgram.matrixPair
    (BlockCoefficientProgram.context p M) (scalarCode p) (QuarticSearch.elements p)
    (QuarticSearch.mem_elements p) M (BlockCoefficientProgram.coefficientCost p m N)
    rfl (coefficientContract p M) regs

theorem program_primitive_runsIn (p : ℕ) [Fact p.Prime] {m N : ℕ}
    (M : Fin m → Fin N → ZMod p) (regs : Fin 24 → Bool) :
    ∃ (next : StructuredProgram.State 24 42) (C : Fin N → Fin N → ZMod p) (d : Fin (N + 1)),
      GoodPair M (splitPair d C) ∧ next.stacks 41 = encodeTuple (scalarCode p) (flattenTable C) ∧
      next.stacks 8 = splitCode d ∧
      Computation.RunsIn (BitProgram.primitive program).step
        (BitProgram.primitiveOverhead program * cost p m N)
        (BitProgram.primitiveCfg program ((inputState p M regs).withPC (some program.entry)))
        (BitProgram.primitiveCfg program (next.withPC none)) := by
  obtain ⟨next, C, d, hgood, hC, hd, hrun⟩ := program_runsIn p M regs
  exact ⟨next, C, d, hgood, hC, hd, BitProgram.primitive_execution program hrun⟩

end SubexponentialSAT.Subexp.BlockSearchConcrete

end OAI.Algorithms

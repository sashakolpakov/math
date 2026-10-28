import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchSetup
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchCoverage

namespace OAI.Algorithms

/-! Preparation and exhaustive search in one fixed instruction table. -/

namespace SubexponentialSAT.Subexp.BlockSearchExecution

open BitProgram StructuredCalls BlockSearch BlockSearchEncoding BlockSearchPredicate
open SubexpTupleRefinement BlockSearchLoop

abbrev command (matrixPair : Cmd 24 42) : Cmd 24 42 :=
  .seq BlockSearchSetup.command (.call (BlockSearchLoop.program matrixPair))

abbrev program (matrixPair : Cmd 24 42) := compiled (command matrixPair) 0 41

def inputState {K : Type*} (ctx : Context) (code : StackEncoding.BlockCode K)
    (alphabet : List K) (N : ℕ) (regs : Fin 24 → Bool) : StructuredProgram.State 24 42 :=
  BlockSearchSetup.inputState ctx (alphabet.map code.block)
    (List.replicate (N * N) true) (List.replicate N true) regs

def searchBound (q N width bound : ℕ) : ℕ :=
  q ^ (N * N) * ((N + 1) * (q ^ N * (24 * (N * width) + bound + 27) +
    35 * N + 62) + 15 * (N * N * width) + 41) + 9

def cost {K : Type*} (code : StackEncoding.BlockCode K) (alphabet : List K)
    (N bound : ℕ) : ℕ :=
  BlockSearchPreparation.cost (alphabet.map code.block)
    (List.replicate (N * N) true) (List.replicate N true) +
      searchBound alphabet.length N code.width bound + 1

theorem program_runsIn {K : Type*} [Field K] [DecidableEq K]
    (matrixPair : Cmd 24 42) (ctx : Context)
    (code : StackEncoding.BlockCode K) (alphabet : List K) (hfull : ∀ x, x ∈ alphabet)
    {m N : ℕ} (M : Fin m → Fin N → K) (bound : ℕ)
    (hdimension : ctx.dimension = List.replicate N true)
    (contract : ∀ (C : Fin N → Fin N → K) (d : Fin (N + 1)),
      CoefficientContract matrixPair ctx (encodeTuple code (flattenTable C)) (splitCode d)
        (encodedTest code alphabet M (encodeTuple code (flattenTable C)) (splitCode d))
        (fun _ => bound) (BlockSearchCoverage.ValidCoefficient code N))
    (regs : Fin 24 → Bool) :
    ∃ (next : StructuredProgram.State 24 42) (C : Fin N → Fin N → K) (d : Fin (N + 1)),
      GoodPair M (splitPair d C) ∧ next.stacks 41 = encodeTuple code (flattenTable C) ∧
      next.stacks 8 = splitCode d ∧
      RunsIn (program matrixPair) (cost code alphabet N bound)
        ((inputState ctx code alphabet N regs).withPC (some (program matrixPair).entry))
        (next.withPC none) := by
  obtain ⟨np, prepared, hnp, hp, h0, h2, hep⟩ := BlockSearchSetup.command_eval ctx
    (alphabet.map code.block) (List.replicate (N * N) true) (List.replicate N true)
    regs (N * N * code.width) (by simpa using hdimension)
  simp only [List.length_replicate] at hp h0
  obtain ⟨next, C, d, hgood, htable, hsplit, ns, hns, hes⟩ :=
    BlockSearchCoverage.program_runsIn matrixPair ctx code alphabet hfull M bound contract
      prepared hp h0 h2
  refine ⟨next, C, d, hgood, htable, hsplit, np + ns + 1, ?_, ?_⟩
  · change np + ns + 1 ≤
      BlockSearchPreparation.cost (alphabet.map code.block)
        (List.replicate (N * N) true) (List.replicate N true) +
          searchBound alphabet.length N code.width bound + 1
    change ns ≤ searchBound alphabet.length N code.width bound at hns
    omega
  · exact compiled_halt_trace
      (hep.seq (Eval.call (BlockSearchLoop.program matrixPair) hes)) 0 41

end SubexponentialSAT.Subexp.BlockSearchExecution

end OAI.Algorithms

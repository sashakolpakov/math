import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeDFSIntegration
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeJointOutput
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeEntrySpace

/-! The fixed outer instruction sequence composes actual parameter setup,
disjoint counting DFS, and full-word positivity. The existing concrete-leaf
contract remains an explicit development obligation, not a final endpoint. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls DisjointReuse

def outerCommand (k : ℕ) (leaf : Cmd 80 1220) : Cmd 80 1220 :=
  .seq (.seq (setupAfterFrontend k) (DFSCountProgram.command k leaf)) answerCommand

noncomputable def countingProgram (cutoff k : ℕ) (leaf : Cmd 80 1220) :=
  entryProgram cutoff (outerCommand k leaf)

def outerBoundary (inputBound bound n : ℕ) : ℕ :=
  max inputBound (1224 * bound + 7 * n + 19)

def outerSpace (inputBound bound n : ℕ) : ℕ :=
  1232 * outerBoundary inputBound bound n + 15

def dfsTime (k n bodyLength thresholdLength leafTime bound visits : ℕ) : ℕ :=
  8 * bodyLength + 16 +
    (visits * (DFSVisit.visitTime k n (SparseCountProgram.formulaBound n k)
      thresholdLength leafTime bound + 1) + 1) + (2 * bound + 7 * n + 18)

/-- Every phase uses the same physical state. The setup's proved final bound
supplies the DFS input cap; the final enlargement occurs once, after counting. -/
theorem outer_from_setup {n setupSteps inputBound bound : ℕ}
    (k : ℕ) (hk : 2 ≤ k) (F : SAT.CNF (Fin n)) (hw : SAT.WidthAtMost k F)
    (a b : State 80 1220)
    (hsetup : DFSVisit.BoundedEval (setupAfterFrontend k) setupSteps a b inputBound)
    (ready : SetupReady k F b) (hs : 0 < sparsifySchedule n)
    (leaf : Cmd 80 1220) (leafTime : ℕ)
    (hstartup : 1220 * inputBound +
      8 * (SubexpNormalizationCorrectness.normalizedBody F).length + 17 ≤ bound)
    (hvisit : DFSCountProgram.visitSpace k n F.card (b.stacks 259).length ≤ bound)
    (hleaf : DFSVisit.LeafContract (n := n) k (b.stacks 259) inputBound
      leaf leafTime bound) :
    ∃ visits total final,
      total ≤ setupSteps +
        dfsTime k n (SubexpNormalizationCorrectness.normalizedBody F).length
          (b.stacks 259).length leafTime bound visits +
        12 * outerBoundary inputBound bound n + 14 ∧
      DFSVisit.BoundedEval (outerCommand k leaf) total a final
        (outerSpace inputBound bound n) ∧
      final.stacks ABI.countStack = countWord (SAT.count F) ∧
      final.stacks ABI.answerStack = [decide (0 < SAT.count F)] ∧
      (decide (0 < SAT.count F) = true ↔ SAT.Satisfiable F) ∧
      (visits : ℝ) ≤
        ((SparseCharging.depthConstant k
          (SparseBudget.chooseM k 1 (sparsifySchedule n) (by decide)) * n + 1 : ℕ) : ℝ) ^ 2 *
          (2 : ℝ) ^ ((n : ℝ) / sparsifySchedule n) := by
  obtain ⟨visits, t, c, ht, hd, hc, hv⟩ := canonical_dfs_execution k hk F hw b ready hs
    leaf leafTime inputBound bound hsetup.final_bound hstartup hvisit hleaf
  have hp := DFSCountProgram.boundedEval_mono hsetup
    (Nat.le_max_left inputBound (1224 * bound + 7 * n + 19))
  have hq := DFSCountProgram.boundedEval_mono hd
    (Nat.le_max_right inputBound (1224 * bound + 7 * n + 19))
  obtain ⟨total, htotal, he, hcount, hanswer, hsat⟩ := append_answer F
    (.seq (setupAfterFrontend k) (DFSCountProgram.command k leaf)) (hp.seq hq) hc
  refine ⟨visits, total, answerResult c, ?_, he, hcount, hanswer, hsat, hv⟩
  change t ≤ dfsTime k n (SubexpNormalizationCorrectness.normalizedBody F).length
    (b.stacks 259).length leafTime bound visits at ht
  change total ≤ setupSteps + t + 12 * outerBoundary inputBound bound n + 14 at htotal
  omega

/-- Compile an actual bounded execution of the fixed outer sequence after the
canonical entry. Both physical outputs and all primitive prefixes use this run. -/
theorem counting_primitive_from_entry {cutoff k n steps bound : ℕ}
    (leaf : Cmd 80 1220) (F : SAT.CNF (Fin n)) (b : State 80 1220)
    (he : DFSVisit.BoundedEval (entryCommand cutoff (outerCommand k leaf)) steps
      (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) b bound)
    (hc : b.stacks ABI.countStack = countWord (SAT.count F))
    (ha : b.stacks ABI.answerStack = [decide (0 < SAT.count F)]) :
    ∃ time : ℕ, ∃ final : LocatedCfg (GuardedCompiler.primitive (countingProgram cutoff k leaf)),
      Computation.Trace
        (locatedStep (GuardedCompiler.primitive (countingProgram cutoff k leaf))) time
        (locatedInit (GuardedCompiler.primitive (countingProgram cutoff k leaf))
          (Encoding.encodeCNF F)) final ∧
      final.config.state = .inl (decide (0 < SAT.count F)) ∧
      final.config.tapes ABI.countStack =
        Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
      final.config.tapes ABI.answerStack =
        Turing.Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
      time ≤ 7 * (steps + 1) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ time →
        Computation.Trace
          (locatedStep (GuardedCompiler.primitive (countingProgram cutoff k leaf))) prefixSteps
          (locatedInit (GuardedCompiler.primitive (countingProgram cutoff k leaf))
            (Encoding.encodeCNF F)) intermediate →
        visitedSpace intermediate ≤ 1220 * (bound + Encoding.formulaBitLength F + 15) := by
  obtain ⟨ht, hs⟩ := entry_bounded_trace_space (outerCommand k leaf) (Encoding.encodeCNF F) b he
  obtain ⟨time, htime, final, hrun, hhalt, hcount, hanswer, hspace⟩ :=
    CompileSpace.compile_word_answer_space (countingProgram cutoff k leaf) ABI.countStack
      ht rfl hc ha hs
  exact ⟨time, final, hrun, hhalt, hcount, hanswer, htime, hspace⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

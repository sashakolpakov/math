import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativePrepared
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram

/-! Connect the actual produced setup frame to canonical exact counting.
The remaining finite leaf-command and numerical-envelope premises are explicit
development seams, to be instantiated by the streamed native leaf integration. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls BinaryArithmetic DisjointReuse

theorem canonical_normalized_body_length {n k : ℕ} (F : SAT.CNF (Fin n))
    (hw : SAT.WidthAtMost k F) :
    (SubexpNormalizationCorrectness.normalizedBody F).length ≤
      SparseCountProgram.formulaBound n k := by
  have hv := SparseDFSRefinement.Valid.normalize (ExecQuantitativeSparsify.formulaList F)
    (ExecQuantitativeSparsify.formulaList_width F k hw)
  rw [canonical_normalized_body]
  exact SparseCountProgram.encodeBody_length_le _ k hv.literal_nodup hv.clause_nodup
    (formulaSet_width_le _ hv.width)

theorem canonical_dfs_execution {n : ℕ} (k : ℕ) (hk : 2 ≤ k)
    (F : SAT.CNF (Fin n)) (hw : SAT.WidthAtMost k F)
    (a : State 80 1220) (ready : SetupReady k F a) (hs : 0 < sparsifySchedule n)
    (leaf : Cmd 80 1220) (leafTime inputBound bound : ℕ)
    (hinput : ∀ i, (a.stacks i).length ≤ inputBound)
    (hstartup : 1220 * inputBound +
      8 * (SubexpNormalizationCorrectness.normalizedBody F).length + 17 ≤ bound)
    (hvisit : DFSCountProgram.visitSpace k n F.card
      (a.stacks 259).length ≤ bound)
    (hleaf : DFSVisit.LeafContract (n := n) k (a.stacks 259) inputBound
      leaf leafTime bound) :
    ∃ visits t b,
      t ≤ 8 * (SubexpNormalizationCorrectness.normalizedBody F).length + 16 +
        (visits * (DFSVisit.visitTime k n (SparseCountProgram.formulaBound n k)
          (a.stacks 259).length leafTime bound + 1) + 1) + (2 * bound + 7 * n + 18) ∧
      DFSVisit.BoundedEval (DFSCountProgram.command k leaf) t a b
        (1224 * bound + 7 * n + 19) ∧
      b.stacks 256 = countWord (SAT.count F) ∧
      (visits : ℝ) ≤
        ((SparseCharging.depthConstant k
          (SparseBudget.chooseM k 1 (sparsifySchedule n) (by decide)) * n + 1 : ℕ) : ℝ) ^ 2 *
          (2 : ℝ) ^ ((n : ℝ) / sparsifySchedule n) := by
  have hwidth := ExecQuantitativeSparsify.formulaList_width F k hw
  have hM : 2 ≤ toNat (a.stacks 259) := by
    rw [ready.threshold]
    exact (SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by decide)).1
  obtain ⟨visits, t, b, ht, he, hout, history⟩ :=
    DFSCountProgram.command_execution k (a.stacks 259) leaf
      (ExecQuantitativeSparsify.formulaList F) a leafTime inputBound bound hk hM hwidth
      ready.dfs_prepared ready.occurrence ready.dimension ready.dimension_length hinput
      (by simpa only [← canonical_normalized_body] using hstartup)
      (by simpa only [ExecQuantitativeSparsify.formulaList_length] using hvisit) hleaf
  have htree := DFSCompletedTree.completed_visits_reciprocal k (sparsifySchedule n)
    hk hs (SparseDFSRefinement.Valid.normalize _ hwidth)
    (by simpa only [ready.threshold] using history)
  refine ⟨visits, t, b, ?_, he, ?_, htree⟩
  · simpa only [← canonical_normalized_body] using ht
  · simpa only [rawCount, ExecQuantitativeSparsify.formulaList_set] using hout

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

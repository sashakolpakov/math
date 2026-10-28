import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSStartup

/-! Concrete count command including startup and physical full-word export.
The actual positivity suffix is appended by the shared native integration.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement DFSVisit
variable {n : ℕ}

def command (k : ℕ) (leaf : Code) : Code :=
  .seq DFSStartup.startup (.seq (loop k leaf) exportCount)

/-- An explicit numerical sum of the four independently proved local resource
requirements. It contains no traversal count or exponential time term. -/
def visitSpace (k n m thresholdLength : ℕ) : ℕ :=
  let P := SparseCountProgram.formulaBound n k
  let Q := SparseDFSBoundarySpace.frontierBound P (m * k)
  (n + 1 + Q + 11 * P + 13) +
    ((SparsePriorityProgram.Selector.selectorCoefficient k + 24) * (P + thresholdLength + 1) ^ 4) +
    (Q + (n + 1) + 620001 * (4 * P + 3) ^ 2) + 100 * (n + 1)

theorem boundedEval_mono {code : Code} {t a b small large}
    (h : BoundedEval code t a b small) (hle : small ≤ large) : BoundedEval code t a b large :=
  ⟨h.eval, fun p c hp hc i => (h.space p c hp hc i).trans hle⟩

private theorem stack_length_le_dataBits {r s l : ℕ} (c : Cfg r s l) (i : Fin s) :
    (c.stacks i).length ≤ dataBits c :=
  Finset.single_le_sum (fun j _ => Nat.zero_le ((c.stacks j).length)) (Finset.mem_univ i)

/-- Startup, every real DFS visit, and the canonical count-word copy form one
actual source execution. The leaf is still an explicit finite-command contract
which the streamed evaluator must discharge before endpoint acceptance. -/
theorem command_execution (k : ℕ) (threshold : List Bool) (leaf : Code)
    (F : RawCNF n) (d : Data) (leafTime inputBound bound : ℕ)
    (hk : 2 ≤ k) (hM : 2 ≤ BinaryArithmetic.toNat threshold)
    (hwidth : ∀ C ∈ F, C.length ≤ k)
    (prepared : DFSStartup.Prepared threshold (ExecCNF.normalize SAT.Literal.negate F) d)
    (hdimension : BinaryArithmetic.toNat (d.stacks 264) =
      4 * BinaryArithmetic.toNat threshold ^ (k - 1))
    (hambient : BinaryArithmetic.toNat (d.stacks 267) = n)
    (hambientLength : (d.stacks 267).length ≤ n + 1)
    (hinput : ∀ i, (d.stacks i).length ≤ inputBound)
    (hstartup : 1220 * inputBound +
      8 * (SparseCountProgram.encodeBody (ExecCNF.normalize SAT.Literal.negate F)).length + 17 ≤ bound)
    (hvisit : visitSpace k n F.length threshold.length ≤ bound)
    (hleaf : LeafContract (n := n) k threshold inputBound leaf leafTime bound) :
    ∃ visits t e,
      t ≤ 8 * (SparseCountProgram.encodeBody (ExecCNF.normalize SAT.Literal.negate F)).length + 16 +
        (visits * (visitTime k n (SparseCountProgram.formulaBound n k)
          threshold.length leafTime bound + 1) + 1) + (2 * bound + 7 * n + 18) ∧
      BoundedEval (command k leaf) t d e (1224 * bound + 7 * n + 19) ∧
      e.stacks 256 = OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord (rawCount F) ∧
      Transitions k (BinaryArithmetic.toNat threshold) visits
        ⟨[⟨ExecCNF.normalize SAT.Literal.negate F, 0⟩], 0⟩ ⟨[], rawCount F⟩ := by
  obtain ⟨a, heval, hboundary, hframe⟩ :=
    DFSStartup.startup_refinement threshold (ExecCNF.normalize SAT.Literal.negate F) d prepared
  have startEval : BoundedEval DFSStartup.startup
      (8 * (SparseCountProgram.encodeBody (ExecCNF.normalize SAT.Literal.negate F)).length + 16)
      d a bound := by
    refine ⟨heval, ?_⟩
    intro t c ht hc i
    exact (DFSStartup.startup_prefix_space d
      (SparseCountProgram.encodeBody (ExecCNF.normalize SAT.Literal.negate F)).length
      inputBound hinput t c (by omega) hc i).trans hstartup
  have aDimension : BinaryArithmetic.toNat (a.stacks 264) =
      4 * BinaryArithmetic.toNat threshold ^ (k - 1) := by
    rw [hframe 264 (by decide) (by decide) (by decide)]
    exact hdimension
  have aAmbient : BinaryArithmetic.toNat (a.stacks 267) = n := by
    rw [hframe 267 (by decide) (by decide) (by decide)]
    exact hambient
  have aParameterLength : (a.stacks 264).length ≤ inputBound := by
    rw [hframe 264 (by decide) (by decide) (by decide)]
    exact hinput 264
  have aAmbientLength : (a.stacks 267).length ≤ n + 1 := by
    rw [hframe 267 (by decide) (by decide) (by decide)]
    exact hambientLength
  have constraints := hvisit
  dsimp [visitSpace] at constraints
  obtain ⟨visits, tl, b, htl, loopEval, finalBoundary, transitions⟩ :=
    DFSNative.normalized_loop k threshold leaf F a leafTime inputBound bound hk hM hwidth hboundary
      aDimension aAmbient aParameterLength aAmbientLength startEval.final_bound
      (by omega) (by omega) (by omega) (by omega) hleaf
  have lengthTotal : (b.stacks 260).length ≤ n + 1 := by
    rw [finalBoundary.total]
    exact binaryNat_length_le (rawCount_le F)
  have bBound := loopEval.final_bound
  obtain ⟨e, exportEval, hout, _, _⟩ := exportCount_eval b
  let exportTime := 2 * (b.stacks 0).length + 2 * (b.stacks 256).length +
    7 * (b.stacks 260).length + 11
  have exportBounded : BoundedEval exportCount exportTime b e (1224 * bound + 7 * n + 19) := by
    refine ⟨exportEval, ?_⟩
    intro t c ht hc i
    have htotal := exportCount_prefix_space b n bound lengthTotal bBound t c
      (by dsimp [exportTime] at ht; omega) hc
    exact (stack_length_le_dataBits c i).trans htotal
  have bound_le : bound ≤ 1224 * bound + 7 * n + 19 := by omega
  have whole := (boundedEval_mono startEval bound_le).seq ((boundedEval_mono loopEval bound_le).seq exportBounded)
  have hExportTime : exportTime ≤ 2 * bound + 7 * n + 18 := by
    have hz := finalBoundary.low_empty 0 (by decide)
    have hb256 := bBound 256
    dsimp [exportTime]
    rw [hz]
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add]
    omega
  refine ⟨visits, _, e, ?_, whole, ?_, transitions⟩
  · omega
  · rw [hout, finalBoundary.total, binaryNat_eq_countWord]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram

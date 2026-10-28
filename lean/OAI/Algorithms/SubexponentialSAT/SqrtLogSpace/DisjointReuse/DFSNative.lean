import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSLoop

/-! Instantiate the loop invariant using actual normalized formulas, concrete
frontier bytes and the count-mass invariant. Only the concrete streamed leaf
execution remains an intermediate contract for integration.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement DFSVisit
variable {n : ℕ}

theorem visitTime_mono (k n a b thresholdLength leafTime bound : ℕ) (hab : a ≤ b) :
    visitTime k n a thresholdLength leafTime bound ≤
      visitTime k n b thresholdLength leafTime bound := by
  have hp := Nat.mul_le_mul_left (SparsePriorityProgram.Selector.selectorCoefficient k)
    (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add_right hab thresholdLength) 1) 4)
  have hq := Nat.mul_le_mul_left 621000
    (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hab) 3) 2)
  have hm := max_le_max hq (le_refl (leafTime + 100 * (n + 1)))
  unfold visitTime
  omega

/-- The pending stack has one formula per retained depth, including all unary
literal encodings. This bound is independent of elapsed visit count. -/
theorem remaining_bytes_le {k M visits total : ℕ} (F : RawCNF n)
    (node : Node n) (rest : List (Node n)) (hM : 2 ≤ M)
    (hwidth : ∀ C ∈ F, C.length ≤ k)
    (htrace : Transitions k M visits
      ⟨[⟨ExecCNF.normalize SAT.Literal.negate F, 0⟩], 0⟩ ⟨node :: rest, total⟩) :
    (pendingBytes rest).length ≤ SparseDFSBoundarySpace.frontierBound
      (SparseCountProgram.formulaBound n k) (F.length * k) := by
  obtain ⟨hvalid, hdepth⟩ := htrace.normalized_pending_invariants F hM hwidth
  have modelTrace := htrace.model
  have ordered := modelTrace.ordered (.cons _ [] .nil (by simp))
  have depthModel : ∀ entry ∈ (Frontier.model ⟨node :: rest, total⟩).pending,
      entry.depth ≤ F.length * k := by
    intro entry hentry
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hentry
    exact hdepth raw hraw
  have hlen := SparseCountProgram.ordered_length_le (F.length * k) ordered depthModel
  have hrest : rest.length ≤ F.length * k + 2 := by
    simp only [Frontier.model, List.length_map, List.length_cons] at hlen
    omega
  exact SparseDFSInvariantSpace.pendingBytes_length_le rest k (F.length * k) hrest
    (fun entry hentry => hvalid entry (List.mem_cons_of_mem node hentry))

/-- A closed outer loop relative to the actual finite leaf command's contract.
All other algorithmic services are the concrete routines in `body_refinement`.
The resource inequalities below are numerical envelopes, discharged by fixed
polynomials before exposing the final machine theorem. -/
theorem normalized_loop (k : ℕ) (threshold : List Bool) (leaf : Code)
    (F : RawCNF n) (d : Data) (leafTime parameterBound bound : ℕ)
    (hk : 2 ≤ k) (hM : 2 ≤ BinaryArithmetic.toNat threshold)
    (hwidth : ∀ C ∈ F, C.length ≤ k)
    (hb : Boundary threshold ⟨[⟨ExecCNF.normalize SAT.Literal.negate F, 0⟩], 0⟩ d)
    (hdimension : BinaryArithmetic.toNat (d.stacks 264) =
      4 * BinaryArithmetic.toNat threshold ^ (k - 1))
    (hambient : BinaryArithmetic.toNat (d.stacks 267) = n)
    (hparameterLength : (d.stacks 264).length ≤ parameterBound)
    (hambientLength : (d.stacks 267).length ≤ n + 1)
    (hbound : ∀ i, (d.stacks i).length ≤ bound)
    (hpop : n + 1 + SparseDFSBoundarySpace.frontierBound (SparseCountProgram.formulaBound n k)
      (F.length * k) + 11 * SparseCountProgram.formulaBound n k + 13 ≤ bound)
    (hselect : (SparsePriorityProgram.Selector.selectorCoefficient k + 24) *
      (SparseCountProgram.formulaBound n k + threshold.length + 1) ^ 4 ≤ bound)
    (hbranch : SparseDFSBoundarySpace.frontierBound (SparseCountProgram.formulaBound n k)
      (F.length * k) + (n + 1) +
      620001 * (4 * SparseCountProgram.formulaBound n k + 3) ^ 2 ≤ bound)
    (hadd : 100 * (n + 1) ≤ bound)
    (hleaf : LeafContract (n := n) k threshold parameterBound leaf leafTime bound) :
    ∃ visits t e, t ≤ visits *
        (visitTime k n (SparseCountProgram.formulaBound n k) threshold.length leafTime bound + 1) + 1 ∧
      BoundedEval (loop k leaf) t d e bound ∧
      Boundary (n := n) threshold ⟨[], rawCount F⟩ e ∧
      Transitions k (BinaryArithmetic.toNat threshold) visits
        ⟨[⟨ExecCNF.normalize SAT.Literal.negate F, 0⟩], 0⟩ ⟨[], rawCount F⟩ := by
  let initial : Frontier n := ⟨[⟨ExecCNF.normalize SAT.Literal.negate F, 0⟩], 0⟩
  let I : Frontier n → Data → Prop := fun s e =>
    (∃ visits, Transitions k (BinaryArithmetic.toNat threshold) visits initial s) ∧
      Boundary threshold s e ∧ (∀ i, (e.stacks i).length ≤ bound) ∧
      BinaryArithmetic.toNat (e.stacks 264) = 4 * BinaryArithmetic.toNat threshold ^ (k - 1) ∧
      BinaryArithmetic.toNat (e.stacks 267) = n ∧
      (e.stacks 264).length ≤ parameterBound ∧ (e.stacks 267).length ≤ n + 1
  have start : I initial d :=
    ⟨⟨0, .refl _⟩, hb, hbound, hdimension, hambient, hparameterLength, hambientLength⟩
  have step : ∀ (node : Node n) rest total e, I ⟨node :: rest, total⟩ e →
      ∃ next t, t ≤ visitTime k n (SparseCountProgram.formulaBound n k)
          threshold.length leafTime bound ∧ ∃ f, BoundedEval (body k leaf) t e f bound ∧
        Transition k (BinaryArithmetic.toNat threshold) ⟨node :: rest, total⟩ next ∧ I next f := by
    intro node rest total e invariant
    obtain ⟨⟨visits, trace⟩, boundary, sourceBound, dimension, ambient,
      parameterLength, ambientLength⟩ := invariant
    have valid := (trace.normalized_pending_invariants F hM hwidth).1 node (List.mem_cons_self)
    have bodyLen := SparseCountProgram.encodeBody_length_le node.formula k valid.literal_nodup
      valid.clause_nodup (formulaSet_width_le node.formula valid.width)
    have pendingLen := remaining_bytes_le F node rest hM hwidth trace
    have inputVolume := SparseSelectorRefinement.inputVolume_le_formulaBound node.formula threshold k
      valid.width valid.literal_nodup valid.clause_nodup
    obtain ⟨next, t, ht, f, he, transition, nextBoundary, setupFrame⟩ :=
      body_refinement threshold leaf node rest total parameterBound leafTime bound e hk hM valid boundary
        dimension ambient parameterLength ambientLength trace.next_sum_le_pow sourceBound
        (by omega)
        ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left inputVolume 4)).trans hselect)
        (by
          have hp := Nat.mul_le_mul_left 620001
            (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.mul_le_mul_left 4 bodyLen) 3) 2)
          omega)
        hadd hleaf
    refine ⟨next, t, ht.trans (visitTime_mono k n _ _ threshold.length leafTime bound bodyLen),
      f, he, transition, ?_⟩
    refine ⟨⟨visits + 1, trace.trans (.cons transition (.refl _))⟩,
      nextBoundary, he.final_bound, ?_, ?_, ?_, ?_⟩
    · rw [setupFrame 264 (by simp)]
      exact dimension
    · rw [setupFrame 267 (by simp)]
      exact ambient
    · rw [setupFrame 264 (by simp)]
      exact parameterLength
    · rw [setupFrame 267 (by simp)]
      exact ambientLength
  obtain ⟨visits, t, total, e, ht, he, transitions, final⟩ := DFSLoop.execute k
    (BinaryArithmetic.toNat threshold) threshold leaf
    (visitTime k n (SparseCountProgram.formulaBound n k) threshold.length leafTime bound)
    bound I hM (fun _ _ h => h.2.1) (fun _ _ h => h.2.2.1) step initial d start
  have total_eq : total = rawCount F := by
    simpa only [rawCount_normalize] using transitions.finished_count
  subst total
  exact ⟨visits, t, e, ht, he, final.2.1, transitions⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative

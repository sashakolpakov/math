import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRankCertificate
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramMagnitudeOffset

namespace OAI.Algorithms

/-! The actual raw owner-fiber length controls separately stored signed
components, so the executed shift is bounded without canonical signs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open PackingCallerProgram LeafParametersProgram BucketProgram.ProducedRank

 theorem fiber_length_ofFn {D : ℕ} (ps : Fin D → ℕ × ℕ) (query start : ℕ) :
    (LayoutOwnerFiberProgram.fiberIndices query start (List.ofFn ps)).length=
      ∑ i : Fin D,if (ps i).1=query then 1 else 0 := by
  induction D generalizing start with
  | zero => simp [LayoutOwnerFiberProgram.fiberIndices]
  | succ D ih =>
    rw [List.ofFn_succ,LayoutOwnerFiberProgram.fiberIndices,Fin.sum_univ_succ]
    by_cases h : (ps 0).1=query <;> simp [h,ih,Nat.add_comm]

 theorem actual_fiber_length (p : Problem) (v : Fin p.n) :
    (LayoutOwnerFiberProgram.fiberIndices v.val 0
      (PackingIncidenceInput.Semantics.nativeEntries p.scopes p.mask)).length=
      (Finset.univ.filter fun i => owner p i=v).card := by
  conv_lhs => rw [← addressPairs_eq p,fiber_length_ofFn]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [addressPair_owner,Fin.val_inj]

 theorem query_fiber_length_le (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (v : Fin (LeafProgram.Query.packingProblem q k hg).n) :
    (LayoutOwnerFiberProgram.fiberIndices v.val 0
      (PackingIncidenceInput.Semantics.nativeEntries q.scopeRows q.forward)).length ≤
      (q.input k).occurrence := by
  rw [show PackingIncidenceInput.Semantics.nativeEntries q.scopeRows q.forward=
    PackingIncidenceInput.Semantics.nativeEntries (LeafProgram.Query.packingProblem q k hg).scopes
      (LeafProgram.Query.packingProblem q k hg).mask from rfl]
  rw [actual_fiber_length]
  exact LeafPackingFiberBounds.query_owner_fiber_le q k hg v

 def queryHeight (q : LeafQueryFrontend.Query) (k : ℕ) : ℕ :=
  2*(q.input k).occurrence*(8*(produce (q.input k)).Q)^(2*(produce (q.input k)).R)

 theorem query_fiber_mass_le (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (v : Fin (LeafProgram.Query.packingProblem q k hg).n) :
    (LayoutOwnerFiberProgram.fiberIndices v.val 0
      (PackingIncidenceInput.Semantics.nativeEntries q.scopeRows q.forward)).length*
        LayoutProgram.constraintMassBound (produce (q.input k)).Q (produce (q.input k)).R ≤
      queryHeight q k := by
  have hQ : 1 ≤ (produce (q.input k)).Q := by have h := hg.2.2.2.2.2.2.1; omega
  calc
    _ ≤ (q.input k).occurrence*(2*(8*(produce (q.input k)).Q)^(2*(produce (q.input k)).R)) :=
      Nat.mul_le_mul (query_fiber_length_le q k hg v)
        (LayoutProgram.constraintMassBound_le _ _ hQ)
    _ = _ := by unfold queryHeight; ring

 theorem query_negative_le {q : LeafQueryFrontend.Query} {k : ℕ}
    {value : ℕ → ℕ → ℤ} {j v : ℕ} {p : LayoutMatrixProgram.Pair}
    (h : FiberRel (PackingIncidenceInput.Semantics.nativeEntries q.scopeRows q.forward)
      value (queryHeight q k) j v p) :
    SubexponentialSAT.BinaryArithmetic.toNat p.2 ≤ queryHeight q k := by
  have hm := h.2
  unfold RowSelectionProgram.pairTotal at hm
  omega

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafPackingFiberBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryPackingInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramControllerResources

namespace OAI.Algorithms

/-! No raw-fiber hypothesis is needed for a produced query: its actual scope
rows are deduplicated, and its parameter fields are the actual native scan. -/
namespace SubexponentialSAT.SqrtLog.LeafPackingFiberBounds
open PackingIncidenceInput LeafStatisticsProgram LeafQueryFrontend

 theorem query_scopes_nodup (q : Query) : ∀ row ∈ q.scopeRows, row.Nodup :=
  LeafScopeResourceBounds.scopes_nodup 1 0 q.codes q.rows q.mark

 theorem query_owner_fiber_le (q : Query) (k : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k))
    (v : Fin (LeafProgram.Query.packingProblem q k hg).n) :
    let p := LeafProgram.Query.packingProblem q k hg
    (Finset.univ.filter fun i : Semantics.Incidences p.scopes p.mask =>
      Semantics.owner p.scopes p.n p.mask p.mask_le i=v).card ≤ (q.input k).occurrence := by
  exact owner_fiber_le _ _ _ _ v

 theorem query_factor_fiber_le (q : Query) (k : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k))
    (e : Fin (Semantics.factorCount q.scopeRows q.forward)) :
    (Finset.univ.filter fun i : Semantics.Incidences q.scopeRows q.forward =>
      Semantics.factor q.scopeRows (BinaryArithmetic.toNat q.ambient) q.forward
        (LeafProgram.Query.packingProblem q k hg).mask_le i=e).card ≤ (q.input k).arity := by
  let hm : q.forward.length ≤ BinaryArithmetic.toNat q.ambient := by
    simp [LeafQueryFrontend.Query.forward, LeafQueryFrontend.highMask]
  calc
    (Finset.univ.filter fun i : Semantics.Incidences q.scopeRows q.forward =>
        Semantics.factor q.scopeRows (BinaryArithmetic.toNat q.ambient) q.forward
          (LeafProgram.Query.packingProblem q k hg).mask_le i=e).card =
        (Finset.univ.filter fun i : Semantics.Incidences q.scopeRows q.forward =>
          Semantics.factor q.scopeRows (BinaryArithmetic.toNat q.ambient) q.forward hm i=e).card := by
      apply congrArg Finset.card
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    _ ≤ (q.input k).arity := by
      have h := factor_fiber_le q.scopeRows q.forward (BinaryArithmetic.toNat q.ambient)
        hm (query_scopes_nodup q) e
      have harity : (q.input k).arity =
          max (LeafStatisticsProgram.Arity.arity q.forward q.scopeRows 0)
            (if (LeafStatisticsProgram.measured q.scopeRows q.forward).uncovered=0 then 0 else 1) := by
        unfold LeafQueryFrontend.Query.input LeafQueryFrontend.numericInput
          LeafQueryFrontend.completedArity LeafQueryFrontend.totals
          LeafStatisticsProgram.measured LeafStatisticsProgram.Finalize.neutralArity
          LeafStatisticsProgram.zeroTotals LeafStatisticsSemantics.zero
        by_cases hz : (LeafStatisticsProgram.variableTotals q.scopeRows 0 q.forward
          { free := 0, occurrence := 0, incidences := 0, uncovered := 0 }).uncovered=0
        · rw [ite_eq_left hz]
        · rw [ite_eq_right hz]
      rw [harity]
      convert h using 1

 theorem query_incidences_le (q : Query) (k : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k)) :
    (LeafProgram.Query.packingProblem q k hg).incidences ≤
      (q.input k).occurrence*(q.input k).freeCount := by
  rw [LeafProgram.Query.packingProblem_incidences, Nat.mul_comm]
  have h := BucketProgram.Controller.Resources.native_rows_le q.scopeRows
    (BinaryArithmetic.toNat q.ambient) q.forward
  rw [PackingIncidenceInput.Stats.native_incidence_count] at h
  exact h

end SubexponentialSAT.SqrtLog.LeafPackingFiberBounds

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRankInventory
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafPackingFiberBoundsQuery

namespace OAI.Algorithms

/-! A produced query determines its actual packing and maximum selected
matrix rank. Coverage, head compatibility, node units, and raw fiber counts
are all proved from the native producer; none is a certificate premise. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram LeafParametersProgram BucketProgram.ProducedRank
open LeafHeadSetupProgram

 theorem query_rank_budget (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (a : Word (LeafProgram.Query.packingProblem q k hg).r (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    16*(Asymptotic.layoutR (q.input k).freeCount:ℝ)*(Asymptotic.L (q.input k).freeCount:ℝ)^2*
      (queryLabelRows q k hg a tail:ℝ) ≤ (q.input k).freeCount :=
  query_rank_budget_of_scan q k hg a tail haN haC
    (LeafPackingFiberBounds.query_owner_fiber_le q k hg)
    (LeafPackingFiberBounds.query_factor_fiber_le q k hg)
    (LeafPackingFiberBounds.query_incidences_le q k hg)

/-- This is the product of the actual attained tables, using all retained
incidence rows; the exponent is the actual query's maximum matrix rank. -/
 theorem query_inventory_le {base : Data} {N B : ℕ}
    (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (a : Word (LeafProgram.Query.packingProblem q k hg).r (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q))
    (t : Fin (LeafProgram.Query.packingProblem q k hg).Q) (H : ℕ)
    {tables : List BucketTupleProgram.HeadTable}
    (ht : let p := LeafProgram.Query.packingProblem q k hg
      ProducedHeads base p.n N p.incidences (rows p a tail) (queryLow q)
        (FiberRel (PackingIncidenceInput.Semantics.nativeEntries p.scopes p.mask)
          (entryNat (packing p a tail) (SubexponentialSAT.Subexp.TailInterval.intervalStart p.r p.Q
            (produce (q.input k)).R) (produce (q.input k)).R t) H)
        B (t.val*p.r) tables)
    (hlen : tables.length=(LeafProgram.Query.packingProblem q k hg).r)
    (hW : H ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141)) :
    (tables.map fun table=>table.buckets.length).prod ≤
      commonBase (LeafProgram.Query.packingProblem q k hg).n H ^ queryLabelRows q k hg a tail :=
  produced_inventory_le (LeafProgram.Query.packingProblem q k hg) a tail (produce (q.input k)).R
    (queryLow q) t H ht hlen hW

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesFinal
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRankMagnitude

namespace OAI.Algorithms

/-! Actual attained bucket inventories fit the constructed resource. The
premise is the native ProducedHeads relation, not a per-table cardinality
bound. All incidence rows remain present in that relation. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open SubexponentialSAT.MulticolorTypes
open LeafQueryFrontend LeafHeadSetupProgram BucketProgram.ProducedRank
noncomputable section

 theorem inventory_le_resources {base : LeafHeadSetupProgram.Data} {N Bout : ℕ}
    (q : Query) (k B qi : ℕ) (hg : LeafParametersProgram.Guard (q.input k))
    (a : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q))
    (t : Fin (problem q k hg).Q) {tables : List BucketTupleProgram.HeadTable}
    (ht : let p := problem q k hg
      ProducedHeads base p.n N p.incidences (ProducedQueryRank.rows p a tail) (lowBytes q)
        (FiberRel (PackingIncidenceInput.Semantics.nativeEntries p.scopes p.mask)
          (entryNat (ProducedQueryRank.packing p a tail) (SubexponentialSAT.Subexp.TailInterval.intervalStart p.r p.Q
            (LeafParametersProgram.produce (q.input k)).R) (LeafParametersProgram.produce (q.input k)).R t)
          (matrixHeight q k)) Bout (t.val*p.r) tables)
    (hlen : tables.length=(problem q k hg).r)
    (hW : matrixHeight q k ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141)) :
    (tables.map fun table=>table.buckets.length).prod ≤
      CostAssembly.assembledWork k (ambient q) (resources q k B qi hg a tail) := by
  have hK := ProducedQueryRank.query_inventory_le q k hg a tail t (matrixHeight q k) ht hlen hW
  apply CostAssembly.labelInventory_le_assembledWork k (ambient q) (resources q k B qi hg a tail) _
  · exact hK
  · exact make_heads_pos q k B _ _ setupC setupD qi ordinaryExponent
  · exact make_bits_pos q k B _ _ setupC setupD qi ordinaryExponent

 theorem enumerate_le_resources {base : LeafHeadSetupProgram.Data} {N Bout : ℕ}
    (q : Query) (k B qi : ℕ) (hg : LeafParametersProgram.Guard (q.input k))
    (a : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q))
    (t : Fin (problem q k hg).Q) {tables : List BucketTupleProgram.HeadTable}
    (ht : let p := problem q k hg
      ProducedHeads base p.n N p.incidences (ProducedQueryRank.rows p a tail) (lowBytes q)
        (FiberRel (PackingIncidenceInput.Semantics.nativeEntries p.scopes p.mask)
          (entryNat (ProducedQueryRank.packing p a tail) (SubexponentialSAT.Subexp.TailInterval.intervalStart p.r p.Q
            (LeafParametersProgram.produce (q.input k)).R) (LeafParametersProgram.produce (q.input k)).R t)
          (matrixHeight q k)) Bout (t.val*p.r) tables)
    (hlen : tables.length=(problem q k hg).r)
    (hW : matrixHeight q k ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141)) :
    (BucketTupleProgram.enumerate tables).length ≤
      CostAssembly.assembledWork k (ambient q) (resources q k B qi hg a tail) := by
  rw [BucketTupleProgram.enumerate_length]
  exact inventory_le_resources q k B qi hg a tail t ht hlen hW

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms

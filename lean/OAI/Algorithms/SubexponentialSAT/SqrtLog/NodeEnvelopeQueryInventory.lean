import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopeProduced
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeAddressedQuery
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesInventory

namespace OAI.Algorithms

/-! The actual addressed query producer supplies the inventory bound used
by the storage proof. No per-table count or matrix evaluator is assumed. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.NodeEnvelope
open SubexponentialSAT BitProgram StructuredCalls MulticolorTypes SubexpSetupStorage
open LeafProgram LeafProgram.NodeNative LeafHeadSetupProgram ProducedQueryResources

variable (query : LeafQueryFrontend.Query) (k occurrence qi : ℕ)
  (hg : LeafParametersProgram.Guard (query.input k))
  (first : Word (problem query k hg).r (problem query k hg).Q)
  (tail : List (Word (problem query k hg).r (problem query k hg).Q))
  (node : Fin (problem query k hg).Q)

theorem query_relation :
    (Native.queryInputsAddressed query k hg first tail node).relation =
      BucketProgram.ProducedRank.FiberRel
        (PackingIncidenceInput.Semantics.nativeEntries query.scopeRows query.forward)
        (BucketProgram.ProducedRank.entryNat
          (ProducedQueryRank.packing (problem query k hg) first tail)
          (SubexponentialSAT.Subexp.TailInterval.intervalStart (problem query k hg).r
            (problem query k hg).Q (LeafParametersProgram.produce (query.input k)).R)
          (LeafParametersProgram.produce (query.input k)).R node)
        (matrixHeight query k) := by
  rw [Native.queryInputsAddressed_relation]
  change BucketProgram.ProducedRank.FiberRel _
    (BucketProgram.ProducedRank.entryNat _ (List.replicate _ true).length _ _) _ = _
  rw [List.length_replicate]
  rfl

theorem query_inventory_bound {a b : NodeNative.Data}
    (pr : Preparation (Native.queryInputsAddressed query k hg first tail node) a b)
    (ha : Ready (Native.queryInputsAddressed query k hg first tail node) a) :
    (pr.head.tables.map fun t=>t.buckets.length).prod ≤
      CostAssembly.assembledWork k (ambient query) (resources query k occurrence qi hg first tail) := by
  have hp := pr.head.produced
  rw [query_relation query k hg first tail node] at hp
  apply inventory_le_resources query k occurrence qi hg first tail node hp pr.head.count
  rw [Native.start_low _ _ _ _ _ _ 141 (by decide)]
  change matrixHeight query k ≤ SubexponentialSAT.BinaryArithmetic.toNat (pr.loaded.stacks 141)
  rw [pr.loaded_words]
  exact ha.heads.offset.ge

theorem query_stream_bound {a b : NodeNative.Data}
    (pr : Preparation (Native.queryInputsAddressed query k hg first tail node) a b)
    (ha : Ready (Native.queryInputsAddressed query k hg first tail node) a)
    (input : ℕ) (hb : WordBound input a) :
    (MomentsAssembly.bucketsInput pr.bucketInputs).length ≤
      streamCap (ambient query) input
        ((problem query k hg).Q*(problem query k hg).r)
        (resources query k occurrence qi hg first tail).headSize
        (CostAssembly.assembledWork k (ambient query) (resources query k occurrence qi hg first tail)) := by
  exact preparation_stream_bound pr ha input _ hb (problem query k hg).hr
    (query_inventory_bound query k occurrence qi hg first tail node pr ha)

end SubexponentialSAT.SqrtLog.NodeEnvelope

end

end OAI.Algorithms

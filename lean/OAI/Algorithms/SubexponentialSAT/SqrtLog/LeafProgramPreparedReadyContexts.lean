import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyShapes
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramConcreteQueryBounds

namespace OAI.Algorithms

/-! Every emitted head context is a canonical list of actual factor IDs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls MomentsAssembly MomentsProgram
open NodeNative LeafHeadSetupProgram BucketTupleProgram
open MomentsAssembly.Relational
attribute [local simp] Fin.coe_ofNat_eq_mod

 theorem preparation_head_contexts {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) :
    ∀ bucket∈pr.bucketInputs,∀ h∈bucket.heads,
      h.context=ProgramEncoding.encodeRecords
        (FactorLoop.records (LeafStatisticsProgram.Arity.decoded h.context)) ∧
      ∀ f∈LeafStatisticsProgram.Arity.decoded h.context,f < s.N := by
  intro bucket hb
  simp only [Preparation.bucketInputs,List.mem_reverse,List.mem_map] at hb
  obtain ⟨heads,hh,rfl⟩ := hb
  refine enumerateFrom_property (fun h=>h.context=ProgramEncoding.encodeRecords
    (FactorLoop.records (LeafStatisticsProgram.Arity.decoded h.context)) ∧
    ∀ f∈LeafStatisticsProgram.Arity.decoded h.context,f < s.N) pr.head.tables [[]] ?_ (by simp) heads hh
  intro table ht h hm
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ht
  simp only [HeadTable.choices,List.mem_reverse,List.mem_map] at hm
  obtain ⟨part,hpart,rfl⟩ := hm
  exact ⟨Concrete.producedHeads_context_canonical pr.head.produced i,
    fun f hf=>Concrete.producedHeads_context_bound pr.head.produced i f hf⟩

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms

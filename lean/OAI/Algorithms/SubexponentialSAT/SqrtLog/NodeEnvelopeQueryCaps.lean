import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopeExecutionCaps
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopePadding

namespace OAI.Algorithms

/-! No supplied bucket, dictionary, support, or scratch size is needed at the
canonical cap for the actual addressed-query preparation. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.NodeEnvelope
open SubexponentialSAT BitProgram StructuredCalls MulticolorTypes SubexpSetupStorage SubexpLiftRing
open LeafProgram LeafProgram.NodeNative LeafHeadSetupProgram ProducedQueryResources
open LeafParametersProgram MomentsAssembly

theorem query_execution_caps (query : LeafQueryFrontend.Query) (k occurrence qi : ℕ)
    (hg : Guard (query.input k))
    (first : Word (problem query k hg).r (problem query k hg).Q)
    (tail : List (Word (problem query k hg).r (problem query k hg).Q))
    (node : Fin (problem query k hg).Q) {a b : NodeNative.Data}
    (pr : Preparation (Native.queryInputsAddressed query k hg first tail node) a b)
    (ha : Ready (Native.queryInputsAddressed query k hg first tail node) a)
    (input : ℕ) (hb : WordBound input a)
    (hJ : a.stacks 243=List.replicate (produce (query.input k)).J true) :
    let A := queryStorageCap query k occurrence qi hg first tail node input
    (∀ v∈pr.bucketInputs,BucketSize A A A v) ∧
    (b.stacks 169).length ≤ A ∧
    (∀ i∈Node.cleanupPorts,(b.stacks i).length ≤ A) ∧
    dictionaryByteEnvelope (baseWidth 3 (produce (query.input k)).t)
      (produce (query.input k)).d
      (ambient query+(produce (query.input k)).t+(produce (query.input k)).J)
      (dictionaryCapacity (Finset.univ : Finset (Fin (ambient query)))
        (produce (query.input k)).t (produce (query.input k)).J) ≤ A ∧
    (bucketsInput pr.bucketInputs).length ≤ A ∧ WordCap A b.stacks := by
  have hs := query_stream_bound query k occurrence qi hg first tail node pr ha input hb
  exact preparation_execution_caps pr ha input _ _ _ _ _ hb hJ hs

end SubexponentialSAT.SqrtLog.NodeEnvelope

end

end OAI.Algorithms

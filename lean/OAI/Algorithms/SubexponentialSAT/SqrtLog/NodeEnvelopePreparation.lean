import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopeWords
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeReplayBase

namespace OAI.Algorithms

/-! The prepared node tape bound follows from actual production and framing.
No execution-time estimate is used to bound its output storage. -/
namespace SubexponentialSAT.SqrtLog.NodeEnvelope
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
open LeafProgram LeafProgram.NodeNative LeafHeadSetupProgram MomentsAssembly

theorem preparation_wordCap {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) (ha : Ready s a) (B H J : ℕ)
    (hb : WordBound B a) (hJ : a.stacks 243=List.replicate J true)
    (hH : (bucketsInput pr.bucketInputs).length ≤ H) :
    WordCap (spaceBudget s B H J) b.stacks := by
  have hw := pr.workspace_bound ha B H J (fun i _=>hb i) hJ hH
  intro i
  by_cases hi : i∈Node.cleanupPorts
  · exact hw i hi
  · rw [pr.frame i hi]
    exact (hb i).trans (by unfold spaceBudget; omega)

/-- The reference run masks only carried collector tapes. The original
collector payloads do not enter the storage bound for this node. -/
theorem preparation_masked_wordCap {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s (NodeNative.masked a) b)
    (ha : Ready s (NodeNative.masked a)) (B J : ℕ)
    (hb : LocalWordBound B a)
    (hJ : (NodeNative.masked a).stacks 243=List.replicate J true) :
    WordCap (spaceBudget s B (bucketsInput pr.bucketInputs).length J) b.stacks :=
  preparation_wordCap pr ha B _ J (masked_wordBound a B hb) hJ le_rfl

end SubexponentialSAT.SqrtLog.NodeEnvelope

end OAI.Algorithms

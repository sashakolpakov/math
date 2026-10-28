import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopeInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopeState

namespace OAI.Algorithms

/-! Actual node production bounds every moment bucket stream directly from
the attained inventory and maximum head size, without a matrix-time bound. -/
namespace SubexponentialSAT.SqrtLog.NodeEnvelope
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage MomentsAssembly
open LeafProgram LeafProgram.NodeNative LeafHeadSetupProgram

def streamCap (n input rCap H K : ℕ) : ℕ :=
  502*(n+1+(2*(rCap*(4*n+20*(7*input+2)^2+4*(2^H*(2*n+1))+7))+2)*K+1)^2

theorem preparation_stream_bound {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) (ha : Ready s a) (input K : ℕ)
    (hb : WordBound input a) (hr : 0 < s.r)
    (hK : (pr.head.tables.map fun t=>t.buckets.length).prod ≤ K) :
    (bucketsInput pr.bucketInputs).length ≤
      streamCap s.n input (s.Q*s.r)
        (LayoutProducedHeads.maxSelected s.n s.Q s.r s.rows s.low) K := by
  have hload : WordBound input (loadedState a) := loaded_wordBound ha input hb
  have hload' : WordBound input (Native.project (loadedState a)) := fun i=>hload i
  have hS := ready_preparation_bound s (Native.project (loadedState a)) ha.heads input hload' hr
  have haddress : s.node.val*s.r+pr.head.tables.length ≤ s.Q*s.r := by
    rw [pr.head.count]
    have h := Nat.mul_le_mul_right s.r s.node.isLt
    nlinarith
  have hbytes := produced_bucket_stream pr.head.produced (s.Q*s.r) (7*input+2)
    (LayoutProducedHeads.maxSelected s.n s.Q s.r s.rows s.low) (s.Q*s.r) K
    haddress hS (fun z hz=>selected_le_max_of_lt _ _ _ _ _ _ hr hz) hK
  simpa only [Preparation.bucketInputs,streamCap] using hbytes

end SubexponentialSAT.SqrtLog.NodeEnvelope

end OAI.Algorithms

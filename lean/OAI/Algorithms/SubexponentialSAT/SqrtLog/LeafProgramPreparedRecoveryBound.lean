import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeCount

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram SubexpLiftRing

theorem recovery_weaken {a : Factor.Data} {count cost width : ℕ}
    (h : ∃r : Residual.Native.Recovery a, r.count=count ∧ r.cost=cost ∧
      ((Residual.Native.countInput a).stacks 194).length+baseWidth 3 r.t=width) :
    ∃r : Residual.Native.Recovery a, r.count=count ∧ r.cost ≤ cost ∧
      ((Residual.Native.countInput a).stacks 194).length+baseWidth 3 r.t ≤ width := by
  obtain ⟨r,hc,ht,hw⟩ := h
  exact ⟨r,hc,ht.le,hw.le⟩

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms

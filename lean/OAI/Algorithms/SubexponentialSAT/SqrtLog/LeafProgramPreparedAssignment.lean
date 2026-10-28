import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopFramed
import OAI.Algorithms.SubexponentialSAT.SqrtLog.FactorResourceTapes
import OAI.Algorithms.SubexponentialSAT.SqrtLog.FactorAssembledCanonical
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentConcrete

namespace OAI.Algorithms

/-! The actual assignment contract at the canonical cap follows from each
reachable input frame. No globally chosen execution or nonempty bucket is
needed to obtain its numeric source bounds. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT SubexpLiftRing SubexpQuarticRing MomentsProgram MomentsAssembly
noncomputable section

theorem canonical_assignment_contract {r Q n d : ℕ}
    (q : Factor.Spec r Q n d) (degree : List Bool) (A : ℕ)
    (headIds : List Bool → List ℕ)
    (zero one : RingProgram.Code (Word (baseWidth 3 q.p.t)) d)
    (high bits : List Bool) :
    Relational.AssignmentContract 3 q.p.t q.p.modulus q.p.cache q.ctx.table q.u q.J
      (AssignmentConcrete.relation q high bits headIds zero one)
      Factor.assignment degree q.width Finset.univ
      (fun frame=>FactorLoop.AssignmentFrame q degree (FactorResource.sourceCap q A A A)
        A A A headIds zero one high bits (FactorLoop.maskedHigh frame))
      (FactorResource.canonicalAssignmentCost q A) := by
  intro c x left seed frame regs hl hs hf hc hx
  have hr := FactorResource.nativeResources_empty hf.engine A
  have hz : A ≤ FactorResource.nativeCap q A A := by unfold FactorResource.nativeCap; omega
  have h := FactorLoop.framed_assignment_contract q degree (FactorResource.sourceCap q A A A)
    A A A (FactorResource.nativeCap q A A) (FactorResource.sourceCap_limits q A A A)
    hr hz headIds zero one high bits
  exact h c x left seed frame regs hl hs hf hc hx

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms

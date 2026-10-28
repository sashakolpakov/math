import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopTapeAssignment
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopTapeMoments
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafIncidenceTapeFootprint

namespace OAI.Algorithms

/-! Closed native assignment and moment footprints, and the resulting
collector-independent assignment execution bound. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing MomentsProgram MomentsAssembly
open ProgramTapeReplay

/-- No instruction of the actual assignment reads or writes a collector tape. -/
theorem assignment_avoids : AvoidsCmd collectorTape Factor.assignment :=
  Tape.assignment IncidenceTapeFootprint.caller

theorem dense_avoids : AvoidsCmd collectorTape (MomentsAssembly.denseCommand Factor.assignment) :=
  Tape.denseCommand Factor.assignment assignment_avoids

/-- The size caps apply only after replacing ignored collector tapes by empty
words. Execution uses the original tapes, with exactly the same runtime. -/
theorem framed_assignment_contract {r Q n d : ℕ}
    (q : Factor.Spec r Q n d) (degree : List Bool)
    (S A T F Z : ℕ) (hl : FactorReady.Limits q S A T F)
    (hr : FactorReady.Resources q (fun _=>[]) F Z) (hAZ : A ≤ Z)
    (headIds : List Bool → List ℕ)
    (zero one : RingProgram.Code (Word (baseWidth 3 q.p.t)) d)
    (metadata702 metadata703 : List Bool) :
    Relational.AssignmentContract 3 q.p.t q.p.modulus q.p.cache q.ctx.table q.u q.J
      (assignmentRelation
        (fun c x=>q.step (assignmentReference metadata702 metadata703 c x))
        (fun c _=>headIds c.head) q.one
        (fun c x=>AssignmentSemantics.coefficient zero one x c.support c.headMask))
      Factor.assignment degree q.width Finset.univ
      (fun high=>AssignmentFrame q degree S A T F headIds zero one metadata702 metadata703 (maskedHigh high))
      (uniformAssignmentBudget n (baseWidth 3 q.p.t) d q.u q.J T
        (concreteCallbackBound q S A T F Z)) :=
  masked_assignment_contract assignment_avoids q degree S A T F Z hl hr hAZ headIds zero one metadata702 metadata703

end SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop

end

end OAI.Algorithms

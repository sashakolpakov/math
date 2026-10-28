import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorCallbackContract
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorReadyCaps

namespace OAI.Algorithms

/-! Closed assignment execution from fixed source data and explicit physical
input invariants. All callback execution and cost premises are discharged. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop
open SubexponentialSAT SubexpLiftRing SubexpQuarticRing MomentsProgram MomentsAssembly
open IdempotentApplyProgram.Bounds
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q n d : ℕ}

def concreteCallbackBound (q : Factor.Spec r Q n d) (S A T F Z : ℕ) : ℕ :=
  Factor.callbackBound q S (FactorReady.callBound q A T F) (FactorReady.callBound q A T F)
    Z (FactorReady.dispatchBound q F)

theorem callback_for_context (q : Factor.Spec r Q n d) (S A T F Z : ℕ)
    (hl : FactorReady.Limits q S A T F)
    (hr : FactorReady.Resources q (fun _=>[]) F Z) (hAZ : A ≤ Z)
    (metadata702 metadata703 : List Bool) (c : AssignmentContext) (x : List Bool) :
    CallbackContract q.u q.J
      (q.step (assignmentReference metadata702 metadata703 c x))
      (engineReady q S A metadata702 metadata703 c x) (fun f=>f ≤ F) T
      (concreteCallbackBound q S A T F Z) := by
  apply Factor.callback_contract q S (FactorReady.callBound q A T F)
    (FactorReady.callBound q A T F) Z (FactorReady.dispatchBound q F) T
    (assignmentReference metadata702 metadata703 c x)
    (engineReady q S A metadata702 metadata703 c x) (fun f=>f ≤ F)
  · intro base hb
    exact ⟨by simpa [assignmentReference] using hb.2.1,
      by simpa [assignmentReference] using hb.2.2.1,
      by simpa [assignmentReference] using hb.2.2.2⟩
  · intro base hb f seed tail regs hf hg ht
    have hg' := FactorBounds.indicator_good_iff.mpr hg
    have resources : FactorReady.Resources q base F Z :=
      ⟨hr.native,hr.ids,hr.width,hr.source,hr.terms,hr.digits,hr.clauseWidths,hr.payload,
        (hb.1.size 707).trans hAZ⟩
    exact ⟨hb.1.callInput hl regs seed tail hf hg' ht,
      hb.1.callCaps resources regs seed tail hf hg' ht⟩

/-- The actual assignment program is now the producer. The only remaining
premises are source data, fixed numeric bounds, and named physical frame facts. -/
theorem closed_assignment_contract (q : Factor.Spec r Q n d) (degree : List Bool)
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
      (AssignmentFrame q degree S A T F headIds zero one metadata702 metadata703)
      (uniformAssignmentBudget n (baseWidth 3 q.p.t) d q.u q.J T
        (concreteCallbackBound q S A T F Z)) := by
  apply assignment_contract 3 q.p.t q.p.modulus q.p.cache q.ctx.table degree q.width
    q.u q.J T (concreteCallbackBound q S A T F Z) q.one
    (FactorBounds.indicator_good_iff.mpr q.oneGood)
    (fun c x=>q.step (assignmentReference metadata702 metadata703 c x))
    (engineReady q S A metadata702 metadata703) (fun _ _ f=>f ≤ F)
    (fun c _=>headIds c.head)
    (fun c x=>AssignmentSemantics.coefficient zero one x c.support c.headMask)
    (AssignmentFrame q degree S A T F headIds zero one metadata702 metadata703)
  · exact callback_for_context q S A T F Z hl hr hAZ metadata702 metadata703
  · intro c x left seed high regs hleft hseed hf hc hx
    exact hf.input q degree S A T F headIds zero one metadata702 metadata703 high
      hl.base_le_source c x hc hx left seed regs hleft hseed
  · intro c x left seed high regs hf hc hx
    exact weight_eq (assignmentEnvironment q degree) left seed high regs c x zero one
      hc hx hf.zeroBytes hf.coefficientOneBytes

end SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop

end

end OAI.Algorithms

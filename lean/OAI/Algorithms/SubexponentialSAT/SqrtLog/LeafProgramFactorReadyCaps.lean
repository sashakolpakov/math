import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorReady

namespace OAI.Algorithms

/-! Common numeric native-call caps, derived without an execution or time
oracle. The ID-dependent dispatcher bound is monotone in its unary ID. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorReady
open SubexponentialSAT BitProgram StructuredCalls MomentsProgram SubexpSetupStorage
open PerturbationAssembly SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native IdempotentApplyProgram.Steps IdempotentApplyProgram.Bounds
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

structure Resources {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (base : Fin 768 → List Bool) (F Z : ℕ) : Prop where
  native : FactorBounds.NativeCaps q.ctx Z
  ids : F ≤ Z
  width : q.bitWidth ≤ Z
  source : (Encoding.encodeList id q.clauses).length ≤ Z
  terms : ∀ ts ∈ q.rows,ts.length ≤ Z
  digits : q.digits.length ≤ Z
  clauseWidths : ∀ ls ∈ q.source,ls.length ≤ Z
  payload : payloadBound q.rawRows q.clauses ≤ Z
  modulus : (base 707).length ≤ Z

def dispatchBound {r Q n d : ℕ} (q : Factor.Spec r Q n d) (F : ℕ) : ℕ :=
  LeafFactorDispatchProgram.budget q.rawRows q.clauses q.mark F

theorem dispatch_monotone {r Q n d : ℕ} (q : Factor.Spec r Q n d) {f F : ℕ} (hf : f ≤ F) :
    LeafFactorDispatchProgram.budget q.rawRows q.clauses q.mark f ≤ dispatchBound q F := by
  unfold dispatchBound LeafFactorDispatchProgram.budget LeafFactorDispatchProgram.dispatchBound
    LeafFactorDispatchProgram.branchBound
  omega

variable {r Q n d : ℕ} {q : Factor.Spec r Q n d} {S A T F Z : ℕ}
  {base : Fin 768 → List Bool}

theorem Input.callCaps (h : Input q S A base) (hr : Resources q base F Z)
    (regs : Fin 40 → Bool) (seed : FactorLoop.Raw n (baseWidth 3 q.p.t) d)
    (tail : List Bool) {f : ℕ} (hf : f ≤ F) (hg : Good Finset.univ q.u q.J seed) (ht : tail.length ≤ T) :
    Factor.CallCaps q (callBound q A T F) (callBound q A T F) Z (dispatchBound q F)
      (FactorLoop.state base regs seed tail (Encoding.encodeNat f).reverse) f := by
  refine ⟨hr.native,hf.trans hr.ids,hr.width,hr.source,hr.terms,hr.digits,hr.clauseWidths,?_,?_,?_,?_,
    dispatch_monotone q hf⟩
  · intro rd
    rw [h.dispatched_eq regs seed tail f rd]
    change (LeafFactorDispatchProgram.selectedPayload q.rawRows q.clauses q.marked q.mark f).length ≤ Z
    exact (selected_length_le _ _ _ _ _).trans hr.payload
  · intro rd
    rw [h.dispatched_eq regs seed tail f rd,fetched_frame _ _ _ _ _ (by decide)]
    exact hr.modulus
  · intro rd
    rw [h.dispatched_eq regs seed tail f rd]
    exact worker_bound base _ seed tail f _ q.u q.J A T F _ h.size hg ht hf
      (selected_length_le q.rawRows q.clauses q.marked q.mark f)
  · intro rd
    rw [h.dispatched_eq regs seed tail f rd]
    exact staged_bound base _ seed tail f _ q.u q.J A T F _ h.size h.stagedSize hg ht hf
      (selected_length_le q.rawRows q.clauses q.marked q.mark f)

end SubexponentialSAT.SqrtLog.LeafProgram.FactorReady

end OAI.Algorithms

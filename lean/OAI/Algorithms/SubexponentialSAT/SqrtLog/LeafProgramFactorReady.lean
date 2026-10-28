import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorReadyPayload

namespace OAI.Algorithms

/-! Fixed node byte invariants imply the complete native callback input for
every eligible ID, every Good accumulator, and every bounded parser tail. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorReady
open SubexponentialSAT BitProgram StructuredCalls MomentsProgram SubexpSetupStorage
open PerturbationAssembly SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native IdempotentApplyProgram.Steps IdempotentApplyProgram.Bounds
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q n d : ℕ} {q : Factor.Spec r Q n d} {S A : ℕ} {base : Fin 768 → List Bool}

private theorem dispatchScratch_ne : ∀ i ∈ FactorDispatch.scratch,
    i ≠ (149 : Fin 768) ∧ i ≠ 150 ∧ i ≠ 151 := by
  intro i hi
  simp only [FactorDispatch.scratch, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num

private theorem callbackBlank_ne :
    ∀ i ∈ ([154,63,64,67,68,62,556] : List (Fin 768)),
      i ≠ 149 ∧ i ≠ 150 ∧ i ≠ 151 := by
  intro i hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

private theorem callbackBlank_mem :
    ∀ i ∈ ([154,63,64,67,68,62,556] : List (Fin 768)),
      i ∈ ([154,63,64,67,68,62,556,684,159] : List (Fin 768)) := by
  intro i hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

theorem Input.dispatched_eq (h : Input q S A base) (regs : Fin 40 → Bool)
    (seed : FactorLoop.Raw n (baseWidth 3 q.p.t) d) (tail : List Bool) (f : ℕ) (rd : Fin 8 → Bool) :
    q.dispatched (FactorLoop.state base regs seed tail (Encoding.encodeNat f).reverse) f rd=
      fetched q base
        (q.dispatched (FactorLoop.state base regs seed tail (Encoding.encodeNat f).reverse) f rd).regs
        seed tail f := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · exact actual_stacks base regs seed tail f rd q.rawRows q.clauses q.marked q.mark
      h.rows h.clauses h.count h.mark h.dispatchWork

theorem Input.callInput {T F f : ℕ} (h : Input q S A base) (hl : Limits q S A T F)
    (regs : Fin 40 → Bool) (seed : FactorLoop.Raw n (baseWidth 3 q.p.t) d)
    (tail : List Bool) (hf : f ≤ F) (hg : Good Finset.univ q.u q.J seed) (ht : tail.length ≤ T) :
    Factor.CallInput q S (callBound q A T F)
      (FactorLoop.state base regs seed tail (Encoding.encodeNat f).reverse) f seed := by
  constructor
  · simpa [FactorLoop.state] using h.rows
  · simpa [FactorLoop.state] using h.clauses
  · simpa [FactorLoop.state] using h.count
  · simpa [FactorLoop.state] using h.mark
  · simpa [FactorLoop.state] using h.flag
  · simp [FactorLoop.state]
  · simp [FactorLoop.state]
  · intro i hi
    have hn := dispatchScratch_ne i hi
    simpa [FactorLoop.state,hn.1,hn.2.1,hn.2.2] using h.dispatchWork i hi
  · intro i hi
    have hn := callbackBlank_ne i hi
    have hh := h.blank i (callbackBlank_mem i hi)
    simpa [FactorLoop.state,hn.1,hn.2.1,hn.2.2] using hh
  · intro rd
    let out := q.dispatched (FactorLoop.state base regs seed tail (Encoding.encodeNat f).reverse) f rd
    rw [h.dispatched_eq regs seed tail f rd]
    have hb := staged_bound base out.regs seed tail f
      (LeafFactorDispatchProgram.selectedPayload q.rawRows q.clauses q.marked q.mark f)
      q.u q.J A T F (payloadBound q.rawRows q.clauses) h.size h.stagedSize hg ht hf
      (selected_length_le q.rawRows q.clauses q.marked q.mark f)
    have H := h.incidence hl
      (workerState base out.regs seed tail f
        (LeafFactorDispatchProgram.selectedPayload q.rawRows q.clauses q.marked q.mark f))
      (worker_agree _ _ _ _ _ _) (worker_factor _ _ _ _ _ _) hf hb
    simpa only [workerState,fetched,FactorLoop.state,out,Function.update_apply,
      show (202 : Fin 768)≠149 by decide,show (202 : Fin 768)≠150 by decide,
      show (202 : Fin 768)≠151 by decide,ite_false] using H
  · intro rd hidx
    rw [h.dispatched_eq regs seed tail f rd]
    exact h.fetched_hash _ seed tail f hidx
  · intro rd hm hidx
    rw [h.dispatched_eq regs seed tail f rd]
    exact h.fetched_marked _ seed tail f hm hidx

end SubexponentialSAT.SqrtLog.LeafProgram.FactorReady

end OAI.Algorithms

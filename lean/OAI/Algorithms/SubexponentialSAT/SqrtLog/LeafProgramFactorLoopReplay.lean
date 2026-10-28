import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopClosed
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay

namespace OAI.Algorithms

/-! Replay the bounded-reference assignment without restricting the unused
collector buffers. No masking command is executed at runtime. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing MomentsProgram MomentsAssembly
open ProgramTapeReplay
attribute [local simp] Fin.coe_ofNat_eq_mod

def collectorTape (i : Fin 768) : Prop :=
  i ∈ ([256,265,301,302,303,304,305] : List (Fin 768))
instance : DecidablePred collectorTape := fun i => inferInstanceAs (Decidable (i ∈ ([256,265,301,302,303,304,305] : List (Fin 768))))

def maskedHigh (high : Fin 768 → List Bool) : Fin 768 → List Bool :=
  rebaseStacks collectorTape (fun _=>[]) high

theorem collector_high (i : Fin 768) (h : collectorTape i) : 56 ≤ i.val := by
  simp only [collectorTape,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem masked_at (high : Fin 768 → List Bool) (i : Fin 768) (h : ¬collectorTape i) :
    maskedHigh high i=high i := by simp [maskedHigh,rebaseStacks,h]

theorem rebase_machine (frame high : Fin 768 → List Bool) (regs : Fin 40 → Bool) (core : Product.Store) :
    rebaseState collectorTape frame (machine regs core high)=
      machine regs core (rebaseStacks collectorTape frame high) := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  by_cases hi : i.val < 56
  · have hn : ¬collectorTape i := fun h=>by have := collector_high i h; omega
    simp [rebaseStacks,machine,hi,hn]
  · simp [rebaseStacks,machine,hi]

theorem rebase_mask (high : Fin 768 → List Bool) :
    rebaseStacks collectorTape high (maskedHigh high)=high := by
  funext i
  by_cases hi : collectorTape i <;> simp [maskedHigh,rebaseStacks,hi]

theorem masked_matches (high : Fin 768 → List Bool) (c : AssignmentContext)
    (h : c.Matches high) : c.Matches (maskedHigh high) := by
  simpa [AssignmentContext.Matches,maskedHigh,rebaseStacks,collectorTape] using h

/-- The actual no-read/no-write footprint is supplied separately. Once it is
proved, this theorem imposes size bounds only on the bounded reference state. -/
theorem masked_assignment_contract {r Q n d : ℕ}
    (safe : AvoidsCmd collectorTape Factor.assignment)
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
        (concreteCallbackBound q S A T F Z)) := by
  have hc := closed_assignment_contract q degree S A T F Z hl hr hAZ headIds zero one metadata702 metadata703
  intro c x left seed high regs hleft hseed hf hmatch hx
  have hmx : maskedHigh high 174=x := (masked_at high 174 (by decide)).trans hx
  obtain ⟨value,hrel,hgood,k,hk,rr,he⟩ := hc c x left seed (maskedHigh high) regs
    hleft hseed hf (masked_matches high c hmatch) hmx
  refine ⟨value,hrel,hgood,k,hk,rr,?_⟩
  have hx := eval_rebase collectorTape safe he high
  rw [rebase_machine,rebase_mask,rebase_machine,
    rebaseStacks_update collectorTape high (maskedHigh high) 174 [] (by decide),rebase_mask] at hx
  exact hx

end SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop

end

end OAI.Algorithms

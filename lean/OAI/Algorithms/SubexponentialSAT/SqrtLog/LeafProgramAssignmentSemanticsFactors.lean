import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentSemanticsCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramIndicator
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramBoundsMultiplier

namespace OAI.Algorithms

/-! The selected factor map matches the runtime dispatcher: hashes first,
one optional direct marked clause, then skipped neutral IDs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open NativeSemantics
open IdempotentApplyProgram.Steps (Context)

variable {p t n d : ℕ} [Fact p.Prime]

def selectedFactor (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : ℕ → Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n)))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (id : ℕ) : Option (Raw (p:=p) (t:=t) (n:=n) (d:=d)) :=
  if h : id < hashes.length then
    some (Indicator.result ctx minus one (incidence id) hashes[id] digits)
  else if marked && decide (id = hashes.length) then
    some (DynamicFold.value
      (Clause.step p t ctx.modulus ctx.cache ctx.table minus one (incidence id) ctx.u ctx.J)
      clause one)
  else none

theorem indicator_good (ctx : Context p t n d) (vars : Finset (Fin n))
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d)) (hone : Good vars ctx.u ctx.J one)
    (hi : ∀ v, Good vars ctx.u ctx.J (incidence v))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t))) :
    Good vars ctx.u ctx.J (Indicator.result ctx minus one incidence ws digits) := by
  have hh := row_fold_good p t ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J
    minus one incidence hone hi ws [] Good.nil
  have ho : IdempotentApplyProgram.Bounds.Good vars ctx.u ctx.J one := ⟨hone.valid,hone.nodup⟩
  have hg := IdempotentApplyProgram.Bounds.prepared_bounded ctx vars minus
    (Indicator.rawHash ctx minus one incidence ws) one hh.valid ho
  have h := IdempotentApplyProgram.Bounds.loopResult_good ctx vars hu hJ
    (Indicator.rawHash ctx minus one incidence ws) _ hh.valid hg.1 digits.reverse []
    (IdempotentApplyProgram.Bounds.good_nil vars ctx.u ctx.J)
  exact ⟨h.1,h.2⟩

theorem selectedFactor_good (ctx : Context p t n d) (vars : Finset (Fin n))
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : ℕ → Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d)) (hone : Good vars ctx.u ctx.J one)
    (hi : ∀ id v, Good vars ctx.u ctx.J (incidence id v))
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n)))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (id : ℕ) (factor : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (h : selectedFactor ctx minus one incidence hashes marked clause digits id = some factor) :
    Good vars ctx.u ctx.J factor := by
  unfold selectedFactor at h
  split at h
  · cases h
    exact indicator_good ctx vars hu hJ minus one _ hone (hi id) _ digits
  · split at h
    · cases h
      exact clause_fold_good p t ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J
        minus one _ hone (hi id) clause one hone
    · simp at h

theorem selectedFactors_good (ctx : Context p t n d) (vars : Finset (Fin n))
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : ℕ → Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d)) (hone : Good vars ctx.u ctx.J one)
    (hi : ∀ id v, Good vars ctx.u ctx.J (incidence id v))
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n)))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t))) (ids : List ℕ) :
    Good vars ctx.u ctx.J
      (selectedRun ctx.modulus ctx.cache ctx.table ctx.u ctx.J
        (selectedFactor ctx minus one incidence hashes marked clause digits) ids one) :=
  selectedRun_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J _ ids
    (fun id _ factor h => selectedFactor_good ctx vars hu hJ minus one incidence hone hi
      hashes marked clause digits id factor h) one hone

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

end OAI.Algorithms

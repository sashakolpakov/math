import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.FactorResourceCaps
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopClosed

namespace OAI.Algorithms

/-! Parser and plan capacities follow actual represented tape lengths. This
includes neutral factor IDs; no restriction to raw hash IDs is required. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorResource
open SubexponentialSAT SubexpLiftRing StructuredCalls
open SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- A unary ID in the actual parser stream is no larger than that stream. -/
theorem id_le_parser_length (ids : List ℕ) {i : ℕ} (hi : i ∈ ids) :
    i ≤ (ProgramEncoding.encodeRecords (FactorLoop.records ids)).length := by
  have hm : Encoding.encodeNat i ∈ FactorLoop.records ids := List.mem_map.mpr ⟨i,hi,rfl⟩
  have h := HashInputProgram.Loop.original_payload_length_le (FactorLoop.records ids) _ hm
  rw [Encoding.length_encodeNat] at h
  exact (Nat.le_succ i).trans h

/-- The plan stream is already present in the staged physical master bank. -/
theorem plans_le_base {r Q n d : ℕ} {q : Factor.Spec r Q n d} {S A : ℕ}
    {base : Fin 768 → List Bool} (h : FactorReady.Input q S A base) :
    (LayoutOwnerFiberProgram.stream q.ps).length ≤ A := by
  have hh := h.stagedSize 136
  rw [h.physical.plans] at hh
  exact hh

/-- Assignment preparation leaves the complete factor-ID source untouched. -/
theorem prepared_parser {r Q n d : ℕ} (q : Factor.Spec r Q n d) (degree : List Bool)
    (high : Fin 768 → List Bool) :
    FactorLoop.preparedAssignment q degree high [] [] 175=high 175 := by
  simp [FactorLoop.preparedAssignment,LeafAssignmentSetupProgram.prepared_stacks,
    FactorLoop.assignmentMachine,MomentsAssembly.machine]

/-- The same physical cap A pays the parser tail and every eligible ID. -/
theorem parser_caps {r Q n d : ℕ} {q : Factor.Spec r Q n d} {S A : ℕ}
    (degree : List Bool) (high : Fin 768 → List Bool) (ids : List ℕ)
    (h : FactorReady.Input q S A (FactorLoop.preparedAssignment q degree high [] []))
    (he : high 175=ProgramEncoding.encodeRecords (FactorLoop.records ids)) :
    (high 175).length ≤ A ∧ ∀ i ∈ ids,i ≤ A := by
  have hh := h.size 175
  rw [prepared_parser] at hh
  refine ⟨hh,?_⟩
  intro i hi
  exact (id_le_parser_length ids hi).trans (he ▸ hh)

/-- The measured budget here is exactly the closed assignment budget used by
framed replay, at the computed source cap. -/
theorem assignmentCost_eq_closed {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A T F Z : ℕ) :
    assignmentCost q A T F Z =
      FactorLoop.uniformAssignmentBudget n (baseWidth 3 q.p.t) d q.u q.J T
        (FactorLoop.concreteCallbackBound q (sourceCap q A T F) A T F Z) := rfl

theorem nativeResources_empty {r Q n d : ℕ} {q : Factor.Spec r Q n d} {S A : ℕ}
    {base : Fin 768 → List Bool} (h : FactorReady.Input q S A base) (F : ℕ) :
    FactorReady.Resources q (fun _=>[]) F (nativeCap q A F) := by
  have hh := nativeResources h F
  exact ⟨hh.native,hh.ids,hh.width,hh.source,hh.terms,hh.digits,hh.clauseWidths,hh.payload,by simp⟩

end SubexponentialSAT.SqrtLog.LeafProgram.FactorResource

end OAI.Algorithms

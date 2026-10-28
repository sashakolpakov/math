import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeBounded
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeSpec

namespace OAI.Algorithms

/-! The checked native mass trace supplies the exact selector MassSpec using
only bounded physical source words and bounded native query time. Metadata
outside the selector ports supplies one common budget for every candidate,
incumbent, queue, and register assignment in the MassSpec quantifiers. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT BitProgram StructuredCalls LeafOuterProgram HashSelectProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

structure BoundedMassWitness (k : ℕ) (a : Data) (score : List Bool) (L Q : ℕ) where
  count : List Bool → ℕ
  queryCost : List Bool → ℕ
  width : List Bool → ℕ
  valid : List Bool → Prop
  z : ℕ
  worker : WorkerEmpty a
  sources : ∀ i, MassSource i → (a.stacks i).length ≤ L
  modulus : BinaryArithmetic.toNat (a.stacks 782)≠0
  queries : MassQueries k (savedRegisters callerRegisters a) count queryCost width valid
  references : ∀ bits∈massRecords a, valid bits
  queryBound : ∀ bits∈massRecords a, queryCost bits ≤ Q
  sum : (List.map count (massRecords a)).sum=z
  capacity : z < 2^massPrecision a
  bytes : SubexpLiftRing.fixedBits (massPrecision a) z=score

private theorem selector_stack_val (i : Fin 9) : (selectorCore.stack i).val=768+i.val := by
  fin_cases i <;> rfl

theorem selector_state_high (frame : Data) (regs : Fin 8 → Bool) (bits : List Bool)
    (best : Entry) (queue : List Bool) (i : Fin 896) (hi : 777 ≤ i.val) :
    (state selectorCore frame regs ⟨bits,[]⟩ best queue).stacks i=frame.stacks i := by
  have hn : ¬∃ j, selectorCore.stack j=i := by
    rintro ⟨j,hj⟩
    have hv := congrArg (fun x : Fin 896 => x.val) hj
    rw [selector_stack_val] at hv
    have := j.isLt
    omega
  simp only [state,embedState_stack_frame _ _ _ _ i hn]

theorem mass_spec_bounded_sources (k : ℕ) (frame : Data) (score : List Bool → List Bool)
    (valid : List Bool → Prop) (B C L Q : ℕ)
    (witnesses : ∀ bits best queue regs, valid bits → Nonempty
      (BoundedMassWitness k (state selectorCore frame regs ⟨bits,[]⟩ best queue)
        (score bits) L Q)) :
    MassSpec (mass k) selectorCore frame score valid B C
      (CounterPrograms.value (frame.stacks 782)*Q+
        overhead L (CounterPrograms.value (frame.stacks 782)) (massPrecision frame) (Q+1)+64) := by
  intro bits best queue regs hv
  obtain ⟨w⟩ := witnesses bits best queue regs hv
  obtain ⟨t,b,ht,he,hs,hr⟩ := mass_eval_bounded_sources k _ L Q
    w.worker w.sources w.modulus w.count w.queryCost w.width w.valid w.queries
    w.references w.queryBound w.z w.sum w.capacity
  rw [w.bytes] at hs
  have hb := selector_result frame regs bits (score bits) best queue b hs hr
  have h782 := selector_state_high frame regs bits best queue 782 (by decide)
  have h785 := selector_state_high frame regs bits best queue 785 (by decide)
  have hbudget : t ≤ CounterPrograms.value (frame.stacks 782)*Q+
      overhead L (CounterPrograms.value (frame.stacks 782)) (massPrecision frame) (Q+1)+64 := by
    simpa only [massPrecision,h782,h785] using ht
  refine ⟨t,hbudget,(fun i => b.regs (selectorCore.register i)),?_⟩
  rw [hb] at he
  exact he

end SubexponentialSAT.SqrtLog.LeafOuterNative

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeMassFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeMeaning

namespace OAI.Algorithms

/-! Bind the native mass trace to the exact selector ABI. The witness below is
an explicit interface for the remaining native query semantics and resource
join, not an asserted source of queries or computed counts. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT BitProgram StructuredCalls LeafOuterProgram HashSelectProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev selectorCore := selector.controller.trial.core

private theorem core_register_val (i : Fin 8) : (selectorCore.register i).val=i.val := by
  fin_cases i <;> rfl
private theorem core_stack_val (i : Fin 9) : (selectorCore.stack i).val=768+i.val := by
  fin_cases i <;> rfl

theorem selector_result (frame : Data) (regs : Fin 8 → Bool) (bits score : List Bool)
    (best : Entry) (queue : List Bool) (out : Data)
    (hs : out.stacks=Function.update (state selectorCore frame regs ⟨bits,[]⟩ best queue).stacks 769 score)
    (hr : ∀ i : Fin 40, (8 : ℕ) ≤ i.val → out.regs i=
      (state selectorCore frame regs ⟨bits,[]⟩ best queue).regs i) :
    out=state selectorCore frame (fun i => out.regs (selectorCore.register i)) ⟨bits,score⟩ best queue := by
  apply CounterForPrograms.data_ext
  · funext i
    by_cases hi : i.val < 8
    · let j : Fin 8 := ⟨i.val,hi⟩
      have hj : selectorCore.register j=i := Fin.ext (core_register_val j)
      rw [←hj,state_register]
    · have hn : ¬∃ j, selectorCore.register j=i := by
        rintro ⟨j,hj⟩
        have hv := congrArg Fin.val hj
        rw [core_register_val] at hv
        have := j.isLt
        omega
      rw [hr i (by omega)]
      simp only [state,embedState_register_frame _ _ _ _ i hn]
  · funext i
    by_cases hi : ∃ j, selectorCore.stack j=i
    · obtain ⟨j,rfl⟩ := hi
      rw [hs,state_stack]
      by_cases hj : j=1
      · subst j
        rw [show selectorCore.stack 1=(769 : Fin 896) from rfl,Function.update_self]
        rfl
      · have hn : selectorCore.stack j≠769 := by
          intro h
          apply hj
          apply Fin.ext
          have hv := congrArg (fun x : Fin 896 => x.val) h
          rw [core_stack_val] at hv
          change 768+j.val=769 at hv
          change j.val=1
          omega
        rw [Function.update_of_ne hn,state_stack]
        fin_cases j <;> simp_all [BinaryArgmin.store]
    · have h769 : i≠769 := by intro h; apply hi; exact ⟨1,h.symm⟩
      rw [hs,Function.update_of_ne h769]
      simp only [state,embedState_stack_frame _ _ _ _ i hi]

structure NativeMassWitness (k : ℕ) (a : Data) (score : List Bool) (budget : ℕ) where
  count : List Bool → ℕ
  queryCost : List Bool → ℕ
  width : List Bool → ℕ
  valid : List Bool → Prop
  z : ℕ
  worker : WorkerEmpty a
  modulus : BinaryArithmetic.toNat (a.stacks 782)≠0
  queries : MassQueries k (savedRegisters callerRegisters a) count queryCost width valid
  references : ∀ bits∈massRecords a, valid bits
  sum : (List.map count (massRecords a)).sum=z
  capacity : z < 2^massPrecision a
  bytes : SubexpLiftRing.fixedBits (massPrecision a) z=score
  cost : massBudget a queryCost width z ≤ budget

theorem mass_spec (k : ℕ) (frame : Data) (score : List Bool → List Bool)
    (valid : List Bool → Prop) (B C budget : ℕ)
    (witnesses : ∀ bits best queue regs, valid bits → Nonempty
      (NativeMassWitness k (state selectorCore frame regs ⟨bits,[]⟩ best queue) (score bits) budget)) :
    MassSpec (mass k) selectorCore frame score valid B C budget := by
  intro bits best queue regs hv
  obtain ⟨w⟩ := witnesses bits best queue regs hv
  obtain ⟨t,b,ht,he,hs,hr⟩ := mass_eval k _ w.worker w.modulus w.count w.queryCost w.width w.valid
    w.queries w.references w.z w.sum w.capacity
  rw [w.bytes] at hs
  have hb := selector_result frame regs bits (score bits) best queue b hs hr
  refine ⟨t,ht.trans w.cost,(fun i => b.regs (selectorCore.register i)),?_⟩
  rw [hb] at he
  exact he

end SubexponentialSAT.SqrtLog.LeafOuterNative

end OAI.Algorithms

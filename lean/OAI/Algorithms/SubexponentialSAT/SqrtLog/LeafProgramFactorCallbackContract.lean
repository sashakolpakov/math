import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorCallbackNative

namespace OAI.Algorithms

/-! The fixed callback contract used by the native factor iterator. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native MomentsProgram
open IdempotentApplyProgram.Steps NativeSemantics

namespace Spec
variable {r Q n d : ℕ} (q : Spec r Q n d)
theorem value_frame (a b : Fin 768 → List Bool)
    (h145 : a 145=b 145) (h702 : a 702=b 702) (h703 : a 703=b 703) (f : ℕ) :
    q.value a f=q.value b f := by
  have hj (j : ℕ) : factorJet q.p q.ps q.packing n f j q.theta a=
      factorJet q.p q.ps q.packing n f j q.theta b :=
    factorJet_frame q.p q.ps q.packing n f j q.theta a b h145 h702 h703
  unfold value Semantics.hashValue Semantics.markedValue
  simp_rw [hj]
end Spec

theorem callback_contract {r Q n d : ℕ} (q : Spec r Q n d) (S A B Z D T : ℕ)
    (reference : Fin 768 → List Bool)
    (ready : (Fin 768 → List Bool) → Prop) (eligible : ℕ → Prop)
    (href : ∀ base, ready base → base 145=reference 145 ∧ base 702=reference 702 ∧ base 703=reference 703)
    (inputs : ∀ base, ready base → ∀ f seed tail regs, eligible f →
      Good Finset.univ q.u q.J seed → tail.length ≤ T →
      CallInput q S B (FactorLoop.state base regs seed tail (Encoding.encodeNat f).reverse) f seed ∧
      CallCaps q A B Z D (FactorLoop.state base regs seed tail (Encoding.encodeNat f).reverse) f) :
    FactorLoop.CallbackContract q.u q.J (q.step reference) ready eligible T
      (callbackBound q S A B Z D) := by
  intro base hbase f seed tail regs hf hseed htail
  have hs : Good Finset.univ q.u q.J seed := FactorBounds.indicator_good_iff.mp hseed
  obtain ⟨hi,hc⟩ := inputs base hbase f seed tail regs hf hs htail
  let a := FactorLoop.state base regs seed tail (Encoding.encodeNat f).reverse
  obtain ⟨out,hgood,hstep,k,z,hk,he,hz,h13,h14,h15⟩ :=
    callback_native q S A B Z D a f seed hs hi hc
  have hvalue : q.value a.stacks f=q.value reference f := by
    obtain ⟨h145,h702,h703⟩ := href base hbase
    apply q.value_frame a.stacks reference
    · simpa [a,FactorLoop.state] using h145
    · simpa [a,FactorLoop.state] using h702
    · simpa [a,FactorLoop.state] using h703
  have hstep' : q.step reference seed f out := by
    change _=Squarefree.canonical q.u q.J (_*q.value a.stacks f) at hstep
    rw [hvalue] at hstep
    exact hstep
  have hz' : z=FactorLoop.state base z.regs out tail [] := by
    cases z with
    | mk zr zs =>
      congr 1
      funext i
      have h := congrFun hz i
      simp only [a,FactorLoop.state] at h ⊢
      by_cases h149 : i=149
      · subst i; simpa using h
      · by_cases h150 : i=150
        · subst i; simpa using h
        · by_cases h151 : i=151
          · subst i; simpa using h
          · simpa [Function.update_of_ne h149,Function.update_of_ne h150,Function.update_of_ne h151] using h
  refine ⟨out,FactorBounds.indicator_good_iff.mpr hgood,hstep',k,hk,z.regs,?_,h13,h14,h15⟩
  exact (congrArg (fun final : Data => Eval callback k a final) hz').mp he

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms

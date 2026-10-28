import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.FactorResourceReady
import OAI.Algorithms.SubexponentialSAT.SqrtLog.FactorResourcePhysical
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorCallbackNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopContract

namespace OAI.Algorithms

/-! The complete measured callback and assignment budgets, with the source
cap computed from the actual readiness dimensions. Constants precede inputs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorResource
open SubexponentialSAT SubexpLiftRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly

noncomputable def callbackCost {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A T F Z : ℕ) : ℕ :=
  Factor.callbackBound q (sourceCap q A T F) (FactorReady.callBound q A T F)
    (FactorReady.callBound q A T F) Z (FactorReady.dispatchBound q F)

noncomputable def assignmentCost {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A T F Z : ℕ) : ℕ :=
  FactorLoop.uniformAssignmentBudget n (baseWidth 3 q.p.t) d q.u q.J T (callbackCost q A T F Z)

theorem dispatchBound_le {r Q n d : ℕ} {q : Factor.Spec r Q n d} {S A : ℕ}
    {base : Fin 768 → List Bool} (h : FactorReady.Input q S A base) (F X : ℕ)
    (hA : A ≤ X) (hF : F ≤ X) : FactorReady.dispatchBound q F ≤ 237*(X+1) := by
  have hr : (Encoding.encodeList id q.rawRows).length ≤ X := by
    rw [← h.rows]; exact (h.size 701).trans hA
  have hc : (Encoding.encodeList id q.clauses).length ≤ X := by
    rw [← h.clauses]; exact (h.size 700).trans hA
  have hn : q.rawRows.length ≤ X := ((Encoding.length_encodeList_lower id q.rawRows).trans hr).trans' (Nat.le_succ _)
  have hm : q.mark ≤ X := by
    have hh := (h.size 705).trans hA
    rw [h.mark,Encoding.length_encodeNat] at hh
    omega
  unfold FactorReady.dispatchBound LeafFactorDispatchProgram.budget
    LeafFactorDispatchProgram.dispatchBound LeafFactorDispatchProgram.branchBound
  omega

theorem callbackCost_polynomial : ∃ C e : ℕ, ∀ {r Q n d : ℕ}
    (q : Factor.Spec r Q n d) (A T F Z X : ℕ) (base : Fin 768 → List Bool),
    FactorReady.Input q (sourceCap q A T F) A base →
    A ≤ X → T ≤ X → F ≤ X → Z ≤ X → n ≤ X → q.J ≤ X →
    FactorReady.seedBound n (baseWidth 3 q.p.t) d q.u q.J ≤ X →
    FactorReady.payloadBound q.rawRows q.clauses ≤ X →
    n*literalRecordBound n (incidenceBitsBound n q.J (d*baseWidth 3 q.p.t)) ≤ X →
    (LayoutOwnerFiberProgram.stream q.ps).length ≤ X →
    callbackCost q A T F Z ≤ C*(X+1)^e := by
  obtain ⟨C,e,he⟩ := branch_physical_polynomial
  refine ⟨C*17^e+269,e+1,?_⟩
  intro r Q n d q A T F Z X base h hA hT hF hZ hn hJ hseed hpayload htable hplans
  have hc := callBound_le q A T F X hA hT hF hseed hpayload
  have hs := sourceCap_le q A T F X hA hT hF hn hseed hpayload htable hplans
  have hb := he h.physical n q.J (FactorReady.callBound q A T F)
    (FactorReady.callBound q A T F) Z (16*(X+1)) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have hb' : FactorBounds.branchBound q.p n q.J (sourceCap q A T F)
      (FactorReady.callBound q A T F) (FactorReady.callBound q A T F) Z ≤
      (C*17^e)*(X+1)^e := by
    apply hb.trans
    calc
      C*(16*(X+1)+1)^e ≤ C*(17*(X+1))^e := by gcongr; omega
      _ = _ := by rw [mul_pow]; ring
  have hd := dispatchBound_le h F X hA hF
  have hp : (X+1)^e ≤ (X+1)^(e+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hi : X+1 ≤ (X+1)^(e+1) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ X+1) (show 1 ≤ e+1 by omega)
  have hb'' := hb'.trans (Nat.mul_le_mul_left (C*17^e) hp)
  unfold callbackCost Factor.callbackBound
  nlinarith

theorem assignmentCost_polynomial : ∃ C e : ℕ, ∀ {r Q n d : ℕ}
    (q : Factor.Spec r Q n d) (A T F Z X : ℕ) (base : Fin 768 → List Bool),
    FactorReady.Input q (sourceCap q A T F) A base →
    A ≤ X → T ≤ X → F ≤ X → Z ≤ X → n ≤ X → q.J ≤ X →
    d*baseWidth 3 q.p.t ≤ X →
    FactorReady.seedBound n (baseWidth 3 q.p.t) d q.u q.J ≤ X →
    FactorReady.payloadBound q.rawRows q.clauses ≤ X →
    n*literalRecordBound n (incidenceBitsBound n q.J (d*baseWidth 3 q.p.t)) ≤ X →
    (LayoutOwnerFiberProgram.stream q.ps).length ≤ X →
    assignmentCost q A T F Z ≤ C*(X+1)^e := by
  obtain ⟨C,e,he⟩ := callbackCost_polynomial
  refine ⟨C+260,e+1,?_⟩
  intro r Q n d q A T F Z X base h hA hT hF hZ hn hJ hwidth hseed hpayload htable hplans
  have hc := he q A T F Z X base h hA hT hF hZ hn hJ hseed hpayload htable hplans
  have hbyte : FactorLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J ≤ X := hseed
  have hpow : 1 ≤ (X+1)^e := Nat.one_le_pow _ _ (by omega)
  have hi : X+1 ≤ (X+1)^(e+1) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ X+1) (show 1 ≤ e+1 by omega)
  unfold assignmentCost FactorLoop.uniformAssignmentBudget
  rw [pow_succ]
  nlinarith

end SubexponentialSAT.SqrtLog.LeafProgram.FactorResource

end OAI.Algorithms

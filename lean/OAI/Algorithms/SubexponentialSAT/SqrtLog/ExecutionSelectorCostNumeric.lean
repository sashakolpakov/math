import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionHashBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeBounds

namespace OAI.Algorithms

/-! Numeric cost of every candidate, every marked clause, and the final count.
Only measured source ports enter L; no bound on untouched caller tapes occurs. -/
namespace SubexponentialSAT.SqrtLog.Execution.SelectorCost
open SubexponentialSAT HashSelectProgram

 theorem overhead_le (L m p H Q : ℕ) (hL : L ≤ H) (hm : m ≤ H) (hp : p ≤ H) :
    LeafOuterNative.overhead L m p (Q+1) ≤ 20000*(H+1)^3*(Q+1) := by
  have hh : LeafOuterNative.overhead L m p (Q+1) ≤
      LeafOuterNative.overhead H H H (Q+1) := by
    unfold LeafOuterNative.overhead
    gcongr
  apply hh.trans
  unfold LeafOuterNative.overhead
  ring_nf
  omega

 theorem mass_le (L m p H Q mass : ℕ) (hL : L ≤ H) (hm : m ≤ H) (hp : p ≤ H)
    (h : mass ≤ m*Q+LeafOuterNative.overhead L m p (Q+1)+64) :
    mass ≤ 21000*(H+1)^3*(Q+1) := by
  have ho := overhead_le L m p H Q hL hm hp
  have hmQ := Nat.mul_le_mul_right Q hm
  have hpoly : H*Q+20000*(H+1)^3*(Q+1)+64 ≤ 21000*(H+1)^3*(Q+1) := by
    ring_nf
    omega
  omega

 theorem inputs_le (count depth rounds : List Bool) (H : ℕ)
    (hc : CounterPrograms.value count ≤ H) (hd : CounterPrograms.value depth ≤ H)
    (hr : CounterPrograms.value rounds ≤ H)
    (hcl : count.length ≤ H) (hdl : depth.length ≤ H) (hrl : rounds.length ≤ H) :
    HashInputs.budget count depth rounds ≤ 200*(H+1)^2 := by
  have hd' := CounterConversions.coreBound_le depth
  have hr' := CounterConversions.coreBound_le rounds
  have hd'' : CounterConversions.runtimeBound depth ≤ 32*(H+1)*(H+1) := by
    unfold CounterConversions.runtimeBound
    gcongr
  have hr'' : CounterConversions.runtimeBound rounds ≤ 32*(H+1)*(H+1) := by
    unfold CounterConversions.runtimeBound
    gcongr
  have hc' : HashAlphabet.budget (CounterPrograms.value count) count.length ≤
      (H+1)*(60*H+60)+2*H+3 := by
    unfold HashAlphabet.budget
    gcongr
  unfold HashInputs.budget
  nlinarith

/-- One H can dominate physical widths, numeric counters, and the actual
candidate count. The query runtime stays linear, even inside marked mass. -/
theorem history_le (count depth rounds : List Bool)
    (p payload L m H Q mass countSteps countBits : ℕ)
    (hcount : 2 ≤ CounterPrograms.value count)
    (hc : CounterPrograms.value count ≤ H) (hd : CounterPrograms.value depth ≤ H)
    (hr : CounterPrograms.value rounds ≤ H)
    (hcl : count.length ≤ H) (hdl : depth.length ≤ H) (hrl : rounds.length ≤ H)
    (hf : CounterPrograms.value count ^ CounterPrograms.value depth ≤ H)
    (hp : p ≤ H) (hpayload : payload ≤ H) (hL : L ≤ H) (hm : m ≤ H)
    (hmass : mass ≤ m*Q+LeafOuterNative.overhead L m p (Q+1)+64)
    (hsteps : countSteps ≤ 5000*(L+Q+1)) (hbits : countBits ≤ Q+1) :
    Hash.budget count depth rounds p payload mass + countSteps + 5*countBits + 11 ≤
      1000000*(H+1)^8*(Q+1) := by
  have hi := inputs_le count depth rounds H hc hd hr hcl hdl hrl
  have hma := mass_le L m p H Q mass hL hm hp hmass
  have hb := Hash.budget_le_polynomial count depth rounds p payload mass hcount
  have hpoly : Hash.polynomialBudget count depth rounds p payload mass ≤
      200*(H+1)^2 + 400*(H+1)*H^2*H^2*((H+1)*H+1)+15+
        controllerBudget H H (21000*(H+1)^3*(Q+1)) (1+(2*(H*H)+2)*H) H H := by
    unfold Hash.polynomialBudget
    dsimp only
    apply Nat.add_le_add
    · gcongr
    · unfold controllerBudget roundsBudget roundBudget selectBudget loadBudget
      gcongr
  have hrest : countSteps + 5*countBits + 11 ≤ 5000*(H+Q+1)+5*(Q+1)+11 := by omega
  apply (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (hb.trans hpoly) countSteps) (5*countBits)) 11).trans
  rw [controllerBudget_callback]
  have hfinal : 200*(H+1)^2 + 400*(H+1)*H^2*H^2*((H+1)*H+1)+15+
      (H*(H+1)*(21000*(H+1)^3*(Q+1))+
      H*(7*(1+(2*(H*H)+2)*H)+(H+1)*(6*H+100*(H+H+1)+14)+5*H+2*H+17)+2)+
      (5000*(H+Q+1)+5*(Q+1)+11) ≤ 1000000*(H+1)^8*(Q+1) := by
    ring_nf
    omega
  omega

end SubexponentialSAT.SqrtLog.Execution.SelectorCost

end OAI.Algorithms

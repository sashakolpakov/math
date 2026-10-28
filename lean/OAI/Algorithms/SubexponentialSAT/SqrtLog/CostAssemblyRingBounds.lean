import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrapBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramCompleteCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblySerialization

namespace OAI.Algorithms

/-! A fixed polynomial bound for the actual ring producer's numerical cost.
The size cap includes the unary numeric bank bound V, so large stored values
are not silently replaced by their binary lengths. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly.RingSetup

open LeafRingSetupProgram LeafParametersProgram CostAssembly.Polynomial

def numberEnvelope (S : ℕ) : ℕ :=
  (workPorts++outputPorts).length*(2*S+3)+(serializationEnvelope S+1)+
  5*(7*S+6+32*(S+1)*(S+1))+(7*S+8)+32

def searchCoefficient : ℕ :=
  IrreducibleSearchBootstrap.preparationConstant*16^4+531441*16^5+1

def coreEnvelope (S : ℕ) : ℕ :=
  scalarBudget S S+1+(7*(2*S)+8)+32+
  (3*(searchCoefficient*(S+1)^10)+7*(2*S)+S*(28*S+14)+15)+
  (7*(2*S)+8)+208000*(S+1)^5*(S+1)^2

def idempotentEnvelope (t W : ℕ) : ℕ :=
  idempotentStartPorts.length*(2*W+3)+(7*W+8)+32+
  IdempotentProgram.polynomialBudget t W+(7*(6*t^2)+8)

def polynomialEnvelope (S : ℕ) : ℕ :=
  let b0 := numberEnvelope S
  let b1 := coreEnvelope S
  let w1 := S+b0+b1+1
  let b2 := constantsBudget w1 (2*S) S
  let w2 := w1+b2+1
  let b3 := nodesBudget w2 S S S
  let w3 := w2+b3+1
  let b4 := idempotentEnvelope S w3
  let w4 := w3+b4+1
  b0+b1+b2+b3+b4+finalDiscard.length*(2*w4+3)+32

theorem producerBudget_le (m : Circuit.Model) (initialWidth V bankWidth S : ℕ)
    (hi : initialWidth ≤ S) (hv : V ≤ S) (hw : bankWidth ≤ S)
    (hl : ∀ i, m.len i ≤ S)
    (ht : m.val 33 ≤ S) (hd : m.val 34 ≤ S) (hq : m.val 21 ≤ S)
    (hfield : 3^(m.val 34) ≤ 16*(m.val 21+1)^2) :
    producerBudget m initialWidth V bankWidth ≤ polynomialEnvelope S := by
  have hser := serialization_budget_le m S hl
  have hsearch := IrreducibleSearchBootstrap.totalCost_sizeDegreeBound hfield
  have h0 : numberBudget m initialWidth V bankWidth ≤ numberEnvelope S := by
    unfold numberBudget numberEnvelope
    gcongr
  have h1 : coreBudget (m.val 33) (m.val 34) bankWidth ≤ coreEnvelope S := by
    unfold coreBudget coreEnvelope scalarBudget
    simp only [RingProgram.ternary_baseWidth]
    change IrreducibleSearchBootstrap.totalCost (m.val 34) ≤
      searchCoefficient*(m.val 21+1)^10 at hsearch
    calc
      _ ≤ 2001*(m.val 33+bankWidth+2)^2+500000*(3*m.val 33+bankWidth+1)^3+1+
          (7*(2*m.val 33)+8)+32+
          (3*(searchCoefficient*(m.val 21+1)^10)+7*(2*m.val 33)+
            m.val 34*(28*m.val 33+14)+15)+
          (7*(2*m.val 33)+8)+208000*(m.val 34+1)^5*(m.val 33+1)^2 := by gcongr
      _ ≤ _ := by gcongr
  have h2 : constantsBudget
      (initialWidth+numberBudget m initialWidth V bankWidth+coreBudget (m.val 33) (m.val 34) bankWidth+1)
      (SubexpLiftRing.baseWidth 3 (m.val 33)) (m.val 34) ≤
      constantsBudget (S+numberEnvelope S+coreEnvelope S+1) (2*S) S := by
    unfold constantsBudget LeafProgram.Constants.budget
    simp only [RingProgram.ternary_baseWidth]
    gcongr
  unfold producerBudget polynomialEnvelope
  dsimp only
  have hn : ∀ W W', W ≤ W' → nodesBudget W (m.val 33) (m.val 34) (m.val 21) ≤ nodesBudget W' S S S := by
    intro W W' hW
    unfold nodesBudget RingNodeProgram.budget RingNodeProgram.stepBudget
    simp only [RingProgram.ternary_baseWidth]
    gcongr
  have he : ∀ W W', W ≤ W' → idempotentBudget (m.val 33) W ≤ idempotentEnvelope S W' := by
    intro W W' hW
    unfold idempotentBudget idempotentEnvelope
    have hp := IdempotentProgram.completeBudget_polynomial (m.val 33) W
    calc
      _ ≤ idempotentStartPorts.length*(2*W+3)+(7*W+8)+32+
          IdempotentProgram.polynomialBudget (m.val 33) W+(7*(6*(m.val 33)^2)+8) := by omega
      _ ≤ _ := by unfold IdempotentProgram.polynomialBudget; gcongr
  let W := initialWidth+numberBudget m initialWidth V bankWidth+
    coreBudget (m.val 33) (m.val 34) bankWidth+1+
    constantsBudget (initialWidth+numberBudget m initialWidth V bankWidth+
      coreBudget (m.val 33) (m.val 34) bankWidth+1)
      (SubexpLiftRing.baseWidth 3 (m.val 33)) (m.val 34)+1
  let W' := S+numberEnvelope S+coreEnvelope S+1+
    constantsBudget (S+numberEnvelope S+coreEnvelope S+1) (2*S) S+1
  have hW : W ≤ W' := by dsimp [W,W']; omega
  have h3 := hn W W' hW
  have h4 := he (W+nodesBudget W (m.val 33) (m.val 34) (m.val 21)+1)
    (W'+nodesBudget W' S S S+1) (by omega)
  dsimp [W,W'] at h3 h4
  gcongr

end SubexponentialSAT.SqrtLog.CostAssembly.RingSetup

end OAI.Algorithms

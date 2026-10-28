import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryMarkedNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyPolynomial

namespace OAI.Algorithms

/-! Numerical bounds for the actual query controllers. All coefficients depend
only on the fixed instruction tables, never on a query or its stored words. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost
open SubexponentialSAT BitProgram StructuredCalls

 theorem branchTime_le (a : Data) (B width ref S : ℕ)
    (hm : (a.stacks 333).length ≤ S) (hB : B ≤ S) (hw : width ≤ S) (hr : ref ≤ S)
    (hN : 2^HighIncidenceProgram.Branches.trueCount (a.stacks 333) ≤ S) :
    Marked.Wide.branchTime a B width ref ≤ 200*(S+1)^3 := by
  have hh : HighIncidenceProgram.Branches.trueCount (a.stacks 333) ≤ S :=
    (List.length_filter_le id _).trans hm
  dsimp only [Marked.Wide.branchTime]
  calc
    _ ≤ 11*S+5+(S*(S+16*(S*(S+1)+1)+28*S+15)+2)+
        (2*(4*S+1)+6*(S*(S+1))+2*S+15) := by gcongr
    _ ≤ 200*(S+1)^3 := by nlinarith [Nat.zero_le (S*S),Nat.zero_le (S*S*S)]

 def controllerCoefficient : ℕ := 100*(cleanupPorts.length+1)

 theorem preparationBudget_le {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : LeafParametersProgram.Guard (q.input k)} {W V L : ℕ}
    (p : Preparation q k a hg W V L) (B S : ℕ)
    (hW : W ≤ S) (hf : p.frontSteps ≤ S) (hp : p.packingSteps ≤ S)
    (ha : p.arithmeticSteps ≤ S) (hc : prepareCost p.out ≤ S)
    (hm : ((prepared p.out).stacks 338).length ≤ S) (hB : B ≤ S) :
    preparationBudget p B ≤ controllerCoefficient*(S+1) := by
  unfold preparationBudget branchBudget cleanupBound controllerCoefficient
  nlinarith [Nat.mul_le_mul_left cleanupPorts.length hW,
    Nat.mul_le_mul_left cleanupPorts.length hf,
    Nat.mul_le_mul_left cleanupPorts.length hp,
    Nat.mul_le_mul_left cleanupPorts.length ha,
    Nat.mul_le_mul_left cleanupPorts.length hc,
    Nat.mul_le_mul_left cleanupPorts.length hm,
    Nat.mul_le_mul_left cleanupPorts.length hB]

 theorem completeBudget_le {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : LeafParametersProgram.Guard (q.input k)} {W V L : ℕ}
    (p : Preparation q k a hg W V L) (branchState : Data) (B width ref S : ℕ)
    (hW : W ≤ S) (hf : p.frontSteps ≤ S) (hp : p.packingSteps ≤ S)
    (ha : p.arithmeticSteps ≤ S) (hc : prepareCost p.out ≤ S)
    (hm : ((prepared p.out).stacks 338).length ≤ S)
    (hmask : (branchState.stacks 333).length ≤ S)
    (hB : B ≤ S) (hw : width ≤ S) (hr : ref ≤ S)
    (hN : 2^HighIncidenceProgram.Branches.trueCount (branchState.stacks 333) ≤ S) :
    preparationBudget p (Marked.Wide.branchTime branchState B width ref) ≤
      (201*controllerCoefficient)*(S+1)^3 := by
  have hpow : 1 ≤ (S+1)^3 := Nat.one_le_pow _ _ (by omega)
  have hS : S ≤ 200*(S+1)^3 := by
    have h := Nat.le_self_pow (by decide : 3≠0) (S+1)
    omega
  have htime := preparationBudget_le p (Marked.Wide.branchTime branchState B width ref)
    (200*(S+1)^3) (hW.trans hS) (hf.trans hS) (hp.trans hS) (ha.trans hS)
    (hc.trans hS) (hm.trans hS) (branchTime_le branchState B width ref S hmask hB hw hr hN)
  calc
    _ ≤ controllerCoefficient*(200*(S+1)^3+1) := htime
    _ ≤ controllerCoefficient*(201*(S+1)^3) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

 theorem residualBound_le (W H samples crt S : ℕ)
    (hW : W ≤ S) (hH : H ≤ S) (hs : samples ≤ S) (hc : crt ≤ S) :
    Residual.Native.residualBound W H samples crt ≤
      (20*Count.Prepare.ports.length+100)*(S+1) := by
  unfold Residual.Native.residualBound Residual.Native.preparationBound
  nlinarith [Nat.mul_le_mul_left Count.Prepare.ports.length hW,
    Nat.mul_le_mul_left Count.Prepare.ports.length hH,
    Nat.mul_le_mul_left Count.Prepare.ports.length hs]

 theorem sampleBudget_le (a : Data) (nodes : ℕ→List Bool) (cost : ℕ→ℕ)
    (maxJet Q S : ℕ) (hQ : Q ≤ S) (hj : maxJet ≤ S)
    (hn : ∀i < Q,(nodes i).length ≤ S) (hc : ∀i < Q,cost i ≤ S)
    (h190 : (a.stacks 190).length ≤ S) (h191 : (a.stacks 191).length ≤ S)
    (h256 : (a.stacks 256).length ≤ S) :
    Residual.Native.sampleBudget a nodes cost maxJet Q ≤ 100*(S+1)^2 := by
  have h := Residual.Native.sampleBudget_uniform a nodes cost maxJet Q S S hn hc
  have hp : Samples.prepareCost a ≤ 4*S+6 := by unfold Samples.prepareCost; omega
  calc
    _ ≤ 4*S+6+S*(S+33*S+6*S+38)+2*S+27 := by
      apply h.trans
      gcongr
    _ ≤ 100*(S+1)^2 := by nlinarith [Nat.zero_le (S*S)]

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost

end OAI.Algorithms

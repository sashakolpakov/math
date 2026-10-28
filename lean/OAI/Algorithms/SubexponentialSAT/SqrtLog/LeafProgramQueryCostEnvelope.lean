import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostControllers
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostRecovery

namespace OAI.Algorithms

/-! One fixed polynomial combines real residual work, all high branches,
reference staging, accumulation, and cleanup. The node cost remains a named
numeric input to be replaced by the separate concrete node theorem. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost
open SubexponentialSAT BitProgram StructuredCalls CostAssembly.Polynomial

 def samplesCap (U K : ℕ) : ℕ := 4*U+6+U*(K+39*U+38)+2*U+27
 def residualCap (U K : ℕ) : ℕ := Residual.Native.residualBound U (65*U+37)
  (samplesCap U K) (recoveryCoefficient*(U+1)^96)
 def branchesCap (U K N : ℕ) : ℕ := 200*(U+residualCap U K+N+1)^3
 def queryCap (U K N : ℕ) : ℕ :=
  10*U+10+controllerCoefficient*(U+branchesCap U K N+1)

 theorem samplesCap_mono {U K V T : ℕ} (hU : U ≤ V) (hK : K ≤ T) :
    samplesCap U K ≤ samplesCap V T := by unfold samplesCap; gcongr
 theorem residualCap_mono {U K V T : ℕ} (hU : U ≤ V) (hK : K ≤ T) :
    residualCap U K ≤ residualCap V T := by
  have hs := samplesCap_mono hU hK
  unfold residualCap Residual.Native.residualBound Residual.Native.preparationBound
  gcongr
 theorem queryCap_mono {U K N V T M : ℕ} (hU : U ≤ V) (hK : K ≤ T) (hN : N ≤ M) :
    queryCap U K N ≤ queryCap V T M := by
  have hr := residualCap_mono hU hK
  unfold queryCap branchesCap
  gcongr

 theorem queryCap_ordinary : Ordinary (fun S=>queryCap S S S) := by
  have hs : Ordinary (fun S=>samplesCap S S) := by
    unfold samplesCap
    exact ordinary_add (ordinary_add (ordinary_add (ordinary_add
      (ordinary_mul (ordinary_const 4) ordinary_id) (ordinary_const 6))
      (ordinary_mul ordinary_id (ordinary_add (ordinary_add ordinary_id
        (ordinary_mul (ordinary_const 39) ordinary_id)) (ordinary_const 38))))
      (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 27)
  have hh : Ordinary (fun S=>65*S+37) :=
    ordinary_add (ordinary_mul (ordinary_const 65) ordinary_id) (ordinary_const 37)
  have hw := ordinary_add (ordinary_add ordinary_id hh) hs
  have hp : Ordinary (fun S=>Residual.Native.preparationBound (S+(65*S+37)+samplesCap S S)) := by
    unfold Residual.Native.preparationBound
    exact ordinary_add (ordinary_add (ordinary_mul
      (ordinary_const (2*Count.Prepare.ports.length+2)) hw)
      (ordinary_const (3*Count.Prepare.ports.length))) (ordinary_const 6)
  have hc : Ordinary (fun S=>recoveryCoefficient*(S+1)^96) :=
    ordinary_mul (ordinary_const recoveryCoefficient)
      (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) 96)
  have hr : Ordinary (fun S=>residualCap S S) := by
    unfold residualCap Residual.Native.residualBound
    exact ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add hh hs) hp) hc)
      (ordinary_mul (ordinary_const 6) hw)) (ordinary_const 9)
  have hb : Ordinary (fun S=>branchesCap S S S) := by
    unfold branchesCap
    exact ordinary_mul (ordinary_const 200) (ordinary_pow
      (ordinary_add (ordinary_add (ordinary_add ordinary_id hr) ordinary_id) (ordinary_const 1)) 3)
  unfold queryCap
  exact ordinary_add (ordinary_add (ordinary_mul (ordinary_const 10) ordinary_id) (ordinary_const 10))
    (ordinary_mul (ordinary_const controllerCoefficient)
      (ordinary_add (ordinary_add ordinary_id hb) (ordinary_const 1)))

 theorem queryCap_polynomial : ∃ C e : ℕ, ∀U K N S : ℕ,
    U ≤ S → K ≤ S → N ≤ S → queryCap U K N ≤ C*(S+1)^e := by
  obtain ⟨C,e,h⟩ := queryCap_ordinary
  exact ⟨C,e,fun U K N S hU hK hN => (queryCap_mono hU hK hN).trans (h S)⟩

 theorem samples_le (a : Data) (nodes : ℕ→List Bool) (cost : ℕ→ℕ)
    (maxJet Q U K : ℕ) (hQ : Q ≤ U) (hj : maxJet ≤ U)
    (hn : ∀i < Q,(nodes i).length ≤ U) (hc : ∀i < Q,cost i ≤ K)
    (h190 : (a.stacks 190).length ≤ U) (h191 : (a.stacks 191).length ≤ U)
    (h256 : (a.stacks 256).length ≤ U) :
    Residual.Native.sampleBudget a nodes cost maxJet Q ≤ samplesCap U K := by
  have h := Residual.Native.sampleBudget_uniform a nodes cost maxJet Q U K hn hc
  have hp : Samples.prepareCost a ≤ 4*U+6 := by unfold Samples.prepareCost; omega
  apply h.trans
  unfold samplesCap
  calc
    _ ≤ 4*U+6+U*(K+33*U+6*U+38)+2*U+27 := by gcongr
    _ = _ := by ring

 theorem residualBound_le_cap (W H samples crt U K : ℕ)
    (hW : W ≤ U) (hH : H ≤ 65*U+37) (hs : samples ≤ samplesCap U K)
    (hc : crt ≤ recoveryCoefficient*(U+1)^96) :
    Residual.Native.residualBound W H samples crt ≤ residualCap U K := by
  unfold residualCap Residual.Native.residualBound Residual.Native.preparationBound
  gcongr

 theorem residual_measured_le (a : Data) (W h : ℕ) (nodes : ℕ→List Bool)
    (cost : ℕ→ℕ) (maxJet Q crt U K : ℕ)
    (hW : W ≤ U) (hm : (a.stacks 338).length ≤ U) (hh : h ≤ U)
    (hQ : Q ≤ U) (hj : maxJet ≤ U) (hn : ∀i < Q,(nodes i).length ≤ U)
    (hc : ∀i < Q,cost i ≤ K)
    (h190 : (a.stacks 190).length ≤ U) (h191 : (a.stacks 191).length ≤ U)
    (h256 : (a.stacks 256).length ≤ U)
    (hcrt : crt ≤ recoveryCoefficient*(U+1)^96) :
    Residual.Native.residualBound W (Residual.Native.highBound a h)
      (Residual.Native.sampleBudget a nodes cost maxJet Q) crt ≤ residualCap U K := by
  apply residualBound_le_cap W _ _ crt U K hW _
    (samples_le a nodes cost maxJet Q U K hQ hj hn hc h190 h191 h256) hcrt
  unfold Residual.Native.highBound
  omega

 theorem branch_le (a : Data) (U K N width ref : ℕ)
    (hm : (a.stacks 333).length ≤ U) (hw : width ≤ U) (hr : ref ≤ U)
    (hN : 2^HighIncidenceProgram.Branches.trueCount (a.stacks 333) ≤ N) :
    Marked.Wide.branchTime a (residualCap U K) width ref ≤ branchesCap U K N := by
  apply branchTime_le
  all_goals omega

 theorem complete_measured_le {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : LeafParametersProgram.Guard (q.input k)} {W V L : ℕ}
    (p : Preparation q k a hg W V L) (branchState : Data) (U K N width ref : ℕ)
    (hW : W ≤ U) (hf : p.frontSteps ≤ U) (hp : p.packingSteps ≤ U)
    (ha : p.arithmeticSteps ≤ U) (hc : prepareCost p.out ≤ U)
    (hm : ((prepared p.out).stacks 338).length ≤ U)
    (hmask : (branchState.stacks 333).length ≤ U) (hw : width ≤ U) (hr : ref ≤ U)
    (hN : 2^HighIncidenceProgram.Branches.trueCount (branchState.stacks 333) ≤ N) :
    10*ref+10+preparationBudget p (Marked.Wide.branchTime branchState (residualCap U K) width ref)
      ≤ queryCap U K N := by
  have hb := branch_le branchState U K N width ref hmask hw hr hN
  have ht := preparationBudget_le p _ (U+branchesCap U K N)
    (hW.trans (Nat.le_add_right _ _)) (hf.trans (Nat.le_add_right _ _))
    (hp.trans (Nat.le_add_right _ _)) (ha.trans (Nat.le_add_right _ _))
    (hc.trans (Nat.le_add_right _ _)) (hm.trans (Nat.le_add_right _ _))
    (hb.trans (Nat.le_add_left _ _))
  unfold queryCap
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost

end OAI.Algorithms

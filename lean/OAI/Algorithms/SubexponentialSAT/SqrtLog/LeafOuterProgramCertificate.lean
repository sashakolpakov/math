import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramBoot

namespace OAI.Algorithms

/-! The concrete callback-to-OrderedCertificate bridge, including its full
parser and Main-wrapper budget. Numerical limits bound existing traces. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram.MainAdapter
open SubexponentialSAT BitProgram StructuredCalls SubexpMainProgram Execution

def leafLimit (payload metadata core : ℕ) : ℕ :=
  100001*(payload+metadata+core+2)+5*payload+12

noncomputable abbrev boot_certificate {c : SubexponentialSAT.SubexpSetupProgram.Config}
    (hc : 896 < SubexponentialSAT.SubexpSetupProgram.helperSize c) {n : ℕ}
    {hr : 32 ≤ workRegs finalExtraRegisters} {F : SubexpOrderedRawPrefix.Formula n}
    (r : Boot c finalExtraRegisters hr F)
    (leafPhases : Phases finalExtraRegisters (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c))
    (core : Cmd 40 896) (test : List Bool → Bool) (coreCost : List Bool → ℕ)
    (valid : List Bool → Prop)
    (hcore : CoreContract core test coreCost valid
      (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2))
      (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24)))
    (hvalid : ∀ bits ∈ r.records, valid bits)
    (hspec : ∀ G ∈ r.leaves, test (ExecSparsifyObserved.encode G)=true ↔
      SAT.Satisfiable (ExecCNF.formulaSet G))
    (prefixLimit splitter leaves payload metadata leafSteps : ℕ)
    (hp : r.startup.prefixSteps+r.startup.setupSteps ≤ prefixLimit)
    (hs : r.steps ≤ splitter) (hl : r.leaves.length ≤ leaves)
    (hb : ∀ bits ∈ r.records, bits.length ≤ payload)
    (hm : (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2)).length+
      (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24)).length ≤ metadata)
    (ht : ∀ bits ∈ r.records, coreCost bits ≤ leafSteps) :
    OrderedCertificate (phases c hr leafPhases)
      (singleLeaf (LeafMain.procedure c hc core)) F
      ⟨prefixLimit,prefixLimit,splitter,leaves,payload,leafLimit payload metadata leafSteps⟩ where
  run := boot_execution hc r leafPhases core test coreCost valid hcore hvalid hspec
  prefixBound := by
    change r.startup.prefixSteps ≤ prefixLimit
    omega
  setupBound := by
    change r.startup.setupSteps ≤ prefixLimit
    omega
  sparsifyBound := hs
  leafCountBound := by
    change r.records.length ≤ leaves
    simpa only [Boot.records,List.length_map] using hl
  payloadBound := hb
  leafBound := by
    intro bits hbits
    change callbackCost coreCost
      (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2))
      (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24)) bits ≤ leafLimit payload metadata leafSteps
    have hbits' := hb bits hbits
    have hsteps := ht bits hbits
    unfold callbackCost leafLimit
    omega

end SubexponentialSAT.SqrtLog.LeafOuterProgram.MainAdapter

end OAI.Algorithms

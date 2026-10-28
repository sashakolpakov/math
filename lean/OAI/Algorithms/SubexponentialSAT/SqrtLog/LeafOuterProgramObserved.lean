import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramCertificate

namespace OAI.Algorithms

/-! The native whole-core contract on the actual observed leaves supplies
all record validity and Boolean-meaning premises of the final certificate. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram.MainAdapter
open SubexponentialSAT BitProgram StructuredCalls SubexpMainProgram Execution

noncomputable abbrev observed_certificate {c : SubexponentialSAT.SubexpSetupProgram.Config}
    (hc : 896 < SubexponentialSAT.SubexpSetupProgram.helperSize c) {n : ℕ}
    {hr : 32  ≤  workRegs finalExtraRegisters} {F : SubexpOrderedRawPrefix.Formula n}
    (r : Boot c finalExtraRegisters hr F)
    (leafPhases : Phases finalExtraRegisters (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c))
    (mass acceptedCount : Cmd 40 896) (coreCost : List Bool → ℕ)
    (hcore : CoreContract (command mass acceptedCount) (inputTest n) coreCost
      (validInput (fun G => G ∈ r.leaves))
      (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2))
      (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24)))
    (prefixLimit splitter leaves payload metadata leafSteps : ℕ)
    (hp : r.startup.prefixSteps+r.startup.setupSteps ≤ prefixLimit)
    (hs : r.steps ≤ splitter) (hl : r.leaves.length ≤ leaves)
    (hb : ∀ bits ∈ r.records, bits.length ≤ payload)
    (hm : (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2)).length+
      (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24)).length ≤ metadata)
    (ht : ∀ bits ∈ r.records, coreCost bits ≤ leafSteps) :
    OrderedCertificate (phases c hr leafPhases)
      (singleLeaf (LeafMain.procedure c hc (command mass acceptedCount))) F
      ⟨prefixLimit,prefixLimit,splitter,leaves,payload,leafLimit payload metadata leafSteps⟩ :=
  boot_certificate hc r leafPhases (command mass acceptedCount) (inputTest n) coreCost
    (validInput (fun G => G ∈ r.leaves)) hcore
    (by
      intro bits hbits
      obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hbits
      exact ⟨G,hG,inputBits_eq_observed G⟩)
    (by
      intro G _
      rw [←inputBits_eq_observed G]
      exact inputTest_spec G)
    prefixLimit splitter leaves payload metadata leafSteps hp hs hl hb hm ht

end SubexponentialSAT.SqrtLog.LeafOuterProgram.MainAdapter

end OAI.Algorithms

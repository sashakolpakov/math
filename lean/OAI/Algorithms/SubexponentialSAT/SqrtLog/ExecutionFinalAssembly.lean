import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionFinalContract
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionFinalCostCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionFinalCostOuter
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionClosure

namespace OAI.Algorithms

/-! Actual prefix, splitter, and leaf composition.  The single remaining
hypothesis is the stated measured native-service contract. -/
namespace SubexponentialSAT.SqrtLog.Execution.Final
open SubexponentialSAT BitProgram StructuredCalls SubexpMainProgram Filter
open LeafOuterProgram Statement
open scoped Topology

theorem certificates_of_history
    (c : SubexponentialSAT.SubexpSetupProgram.Config)
    (hc : 896 < SubexponentialSAT.SubexpSetupProgram.helperSize c)
    (mass acceptedCount : Cmd 40 896) (Ct At : ℝ) (dt : ℕ)
    (hCt : 1 ≤ Ct) (hAt : 0 ≤ At) (hdt : 0 < dt)
    (hsupply : ObservedHistoryContract c mass acceptedCount Ct At dt) :
    ∃ C A : ℝ, ∃ d : ℕ, 1 ≤ C ∧ 0 < A ∧ 0 < d ∧
      ∀ᶠ n : ℕ in atTop, ∀ F : SubexpOrderedRawPrefix.Formula n,
        ExecSunflowerSearch.RawWidthAtMost c.k F →
        ∃ b : Budget, ∃ _cert : OrderedCertificate
          (phases c (by decide) (finalLeafPhases c hc mass acceptedCount))
          (singleLeaf (LeafMain.procedure c hc (command mass acceptedCount))) F b,
          (b.total : ℝ) ≤ runtimeBound C A d (SubexpOrderedRawPrefix.bitLength F) n := by
  obtain ⟨Cs,ds,p,hcore⟩ := eventually_core_nontrivial_sparse
  obtain ⟨q,hq⟩ := occurrence_power c
  obtain ⟨Cp,qp,hCp,hqp,hboot⟩ := eventually_boot c finalExtraRegisters (by decide)
  let C1 : ℝ := 108+2*Ct
  let A1 : ℝ := At+1
  let d1 := p+dt+1
  have hC1 : 1 ≤ C1 := by dsimp [C1]; linarith
  have hA1 : 0 ≤ A1 := by dsimp [A1]; linarith
  obtain ⟨C,A,d,hC,hA,hd,houter⟩ := FinalCost.outer_budget_bound
    (Cp:=(Cp:ℝ)) (C:=C1) (A:=A1) (Nat.cast_nonneg Cp) hC1 hA1 qp d1
  refine ⟨C,A,d,hC,hA,hd,?_⟩
  filter_upwards [hcore q,hboot,CodeSetupOuterCost.setupMajorant_target Cs ds q,hsupply]
    with n hncore hnboot hnsetup hnsupply
  intro F hF
  obtain ⟨r,hP,hS,hN,_⟩ := hnboot F hF
  let nw := r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2)
  let Bw := r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24)
  let cost := tailCost Ct At dt n nw Bw
  let setup := CodeSetupOuterCost.setupMajorant Cs ds q n
  let coreCost := coreLimit setup p nw Bw cost
  have hactual : MainAdapter.CoreContract (command mass acceptedCount) (inputTest n)
      coreCost (validInput (fun G => G ∈ r.leaves)) nw Bw := by
    apply hncore (occurrence c n) nw Bw mass acceptedCount
      (fun G => G ∈ r.leaves) cost
    · exact boot_ambient r
    · exact boot_occurrence r
    · exact occurrence_pos c n
    · exact hq n
    · exact fun G hG hno => boot_leaf_count r G hG hno
    · exact fun G hG a hin hne hno => hnsupply F hF r G hG a hin hne hno
  let L := SubexpOrderedRawPrefix.bitLength F
  let P := r.startup.prefixSteps+r.startup.setupSteps
  let W := L+P+r.steps
  have hword : SubexponentialSAT.SubexpSetupStorage.WordBound W r.final := by
    have hh := boot_wordBound r
    convert hh using 1 ; dsimp [W,L,P] ; omega
  have hmeta : nw.length+Bw.length ≤ 2*W := by
    have h1 := hword (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2)
    have h2 := hword (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24)
    dsimp [nw,Bw]
    omega
  have hbits : ∀ bits ∈ r.records, bits.length ≤ W := by
    intro bits hbits
    have hh := boot_payload_bound r bits hbits
    dsimp [W,L,P]
    omega
  let R := Nat.ceil (runtimeBound C1 A1 d1 (3*W+1) n)
  have hcost : ∀ bits ∈ r.records, coreCost bits ≤ R := by
    intro bits hbits'
    have hsmall := hbits bits hbits'
    have hi : bits.length+nw.length+Bw.length+1 ≤ 3*W+1 := by omega
    have hh := FinalCost.coreLimit_le_runtimeBound hCt hAt p dt n setup hdt
      nw Bw bits cost hnsetup (le_refl _)
    have hm : runtimeBound C1 A1 d1 (bits.length+nw.length+Bw.length+1) n ≤
        runtimeBound C1 A1 d1 (3*W+1) n := by
      unfold runtimeBound
      gcongr
    have hr := (hh.trans hm).trans (Nat.le_ceil (runtimeBound C1 A1 d1 (3*W+1) n))
    exact_mod_cast hr
  let b : Budget := ⟨P,P,r.steps,r.leaves.length,W,MainAdapter.leafLimit W (2*W) R⟩
  let cert : OrderedCertificate
      (phases c (by decide) (finalLeafPhases c hc mass acceptedCount))
      (singleLeaf (LeafMain.procedure c hc (command mass acceptedCount))) F b :=
    MainAdapter.observed_certificate hc r (finalLeafPhases c hc mass acceptedCount)
      mass acceptedCount coreCost hactual P r.steps r.leaves.length W (2*W) R
      (le_refl _) (le_refl _) (le_refl _) hbits hmeta hcost
  refine ⟨b,cert,?_⟩
  have hP' : (P:ℝ) ≤ (Cp:ℝ)*((L:ℝ)+1)^qp := by exact_mod_cast hP
  have hS' : (r.steps:ℝ) ≤ 3617*((L:ℝ)+1)^2*(2:ℝ)^(130*runtimeScale n) := by
    change (r.steps:ℝ) ≤ 3617*
      (((ExecSparsifyObserved.encode F).length:ℝ)+1)^2*(2:ℝ)^(130*runtimeScale n) at hS
    apply hS.trans
    gcongr
    exact_mod_cast observed_body_le_input F
  exact houter L n P r.steps r.leaves.length hP' hS' hN

end SubexponentialSAT.SqrtLog.Execution.Final

end OAI.Algorithms

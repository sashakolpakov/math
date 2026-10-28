import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramHistoryComplete
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramInputTest

namespace OAI.Algorithms

/-! The exact whole-core contract for the concrete outer instruction table.
Its remaining premise is the measured native mass/count service supply. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls Filter
open scoped Topology

theorem eventually_core_history_contract :
    ∃ C d p : ℕ, ∀ q : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ B (nw Bw : List Bool) (mass acceptedCount : Cmd 40 896)
        (admissible : ExecCNF.Formula (SAT.Literal (Fin n)) → Prop)
        (tailCost : List Bool → ℕ),
      BinaryArithmetic.toNat nw=n → BinaryArithmetic.toNat Bw=B →
      0 < B → B ≤ Asymptotic.L n^q →
      (∀ F, admissible F → F.length ≤ n*B) →
      (∀ F, admissible F → ∀ a,
        MainAdapter.CoreInput a (inputBits F) nw Bw →
        HistorySupply F B mass acceptedCount a (tailCost (inputBits F))) →
      MainAdapter.CoreContract (command mass acceptedCount) (inputTest n)
        (coreLimit (CodeSetupOuterCost.setupMajorant C d q n) p nw Bw tailCost)
        (validInput admissible) nw Bw := by
  obtain ⟨C,d,p,hcomplete⟩ := eventually_command_history_eval
  refine ⟨C,d,p,?_⟩
  intro q
  filter_upwards [hcomplete q] with n hn
  intro B nw Bw mass acceptedCount admissible tailCost hnw hBw hB hBq hm hsupply bits hvalid a hin
  obtain ⟨F,hF,rfl⟩ := hvalid
  obtain ⟨steps,b,bit,he,hsteps,hbit,hsat⟩ :=
    hn F B nw Bw mass acceptedCount a (tailCost (inputBits F)) hin hnw hBw hB
      (hm F hF) hBq (hsupply F hF a hin)
  have hformula : a.stacks 784=inputBits F := by simp only [hin 784]; rfl
  have hanswer : bit=inputTest n (inputBits F) := by
    have htest := inputTest_spec F
    have heq : (bit=true) ↔ (inputTest n (inputBits F)=true) := hsat.trans htest.symm
    cases bit <;> cases hh : inputTest n (inputBits F)
    · rfl
    · have hbad : (false : Bool)=true := heq.mpr hh
      cases hbad
    · have hbad : (false : Bool)=true := hh ▸ heq.mp rfl
      cases hbad
    · rfl
  refine ⟨steps,?_,b,he,?_⟩
  · simpa only [hformula,coreLimit,inputBits] using hsteps
  · simpa only [hanswer] using hbit

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms

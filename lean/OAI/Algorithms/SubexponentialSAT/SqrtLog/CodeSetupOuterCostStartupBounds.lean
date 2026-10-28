import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupOuterCostPolynomial
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramStart

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSetupOuterCost
open SubexponentialSAT

theorem record_lengths (records : List (List Bool)) :
    (records.map List.length).sum ≤ (Encoding.encodeList id records).length := by
  induction records with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons,List.sum_cons,Encoding.length_encodeList_cons,id_eq]
    omega

theorem count_budget (W : ℕ) (records : List (List Bool))
    (hW : (Encoding.encodeList id records).length ≤ W) :
    LeafProgram.ClauseCount.budget records+1 ≤ 100*(W+1)^2 := by
  have hs := record_lengths records
  have hn := Encoding.length_encodeList_lower id records
  have hc : SubexpScopeCountSetup.countBudget records ≤ 17*W+10 := by
    unfold SubexpScopeCountSetup.countBudget SubexpSunflowerProgram.CountRecords.loopSteps
    omega
  unfold LeafProgram.ClauseCount.budget
  nlinarith

def startupConstant : ℕ := 100000000000000000000

theorem startBudget_bound (W : ℕ) (records : List (List Bool))
    (hW : (Encoding.encodeList id records).length ≤ W) :
    LeafOuterProgram.startBudget W records ≤ startupConstant*(W+1)^4 := by
  have hc := count_budget W records hW
  dsimp only [LeafOuterProgram.startBudget,LeafOuterProgram.prepareHashBudget]
  calc
    _ ≤ 100*(W+1)^2+
        (10000000000*(W+100*(W+1)^2+1)^2+1+
          1536*(W+100*(W+1)^2+(10000000000*(W+100*(W+1)^2+1)^2+1))+2348)+
        9*(W+100*(W+1)^2+
          (10000000000*(W+100*(W+1)^2+1)^2+1+
          1536*(W+100*(W+1)^2+(10000000000*(W+100*(W+1)^2+1)^2+1))+2348))+8 := by
      gcongr
    _ ≤ _ := by unfold startupConstant; ring_nf; omega

end SubexponentialSAT.SqrtLog.CodeSetupOuterCost

end OAI.Algorithms

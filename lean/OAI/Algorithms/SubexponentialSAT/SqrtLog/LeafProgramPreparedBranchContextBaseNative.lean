import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchContextBase
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchCountQuery

namespace OAI.Algorithms

/-! The native branch context is assembled from a proved residual command
contract and the actual prepared-state frame. Its loop cost and output width
are explicit, and the sum uses every original-coordinate high assignment. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchContext
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
noncomputable section

variable {q : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Query.Preparation q k initial hg W V L)

 def budget (stepBudget stepWidth : ℕ) : ℕ :=
  Marked.Wide.branchTime (base p) stepBudget stepWidth (Query.Width.incomingWidth p)

 def width (stepWidth : ℕ) : ℕ :=
  2^(HighIncidenceProgram.Branches.trueCount q.forward.reverse)*(stepWidth+1)

 def ofResidualSpec (residual : Cmd 40 768) (original : Factor.Data)
    (hf : ∀i,Query.Protected i → i≠323 → initial.stacks i=original.stacks i)
    (hb : ∀i,i∈blankPorts → initial.stacks i=[])
    (hw : ∀i,(initial.stacks i).length ≤ W)
    (stepBudget stepWidth : ℕ) (value : ℕ → ℕ) (count : ℕ)
    (hs : LeafBranchProgram.ResidualSpec LeafBranchProgram.Wide.fixedPorts residual
      (List.replicate (HighIncidenceProgram.Branches.trueCount q.forward.reverse) 1)
      (Residual.Branch.Invariant (base p)) stepBudget stepWidth value)
    (hc : LeafBranchProgram.rankSum value 0
      (2^HighIncidenceProgram.Branches.trueCount q.forward.reverse)=count) :
    Marked.Wide.BranchContext residual (base p) (Query.ProtectedWork original)
      count (budget p stepBudget stepWidth) (width (q:=q) stepWidth) := by
  have hm := base_mask p (hb 333 (by simp [blankPorts]))
  have he := base_empty p hb
  exact {
    inv := Residual.Branch.Invariant (base p)
    stepBudget := stepBudget
    stepWidth := stepWidth
    referenceBound := Query.Width.incomingWidth p
    value := value
    counterStable := Residual.Branch.counterStable (base p)
    massStable := Residual.Branch.massStable (base p)
    residualSpec := by simpa only [hm] using hs
    initialized := Residual.Branch.initialized (base p)
    referenceLength := fun b hi =>
      (congrArg List.length (hi.2 321 (by decide))).le.trans (base_reference_length p hw)
    counterEmpty := he.1
    counterScratchEmpty := he.2.1
    massEmpty := he.2.2.1
    nextEmpty := he.2.2.2.1
    addScratchEmpty := he.2.2.2.2
    sourceFrame := fun b hi => hi.2 320 (by decide)
    accumulatorFrame := fun b hi => hi.2 322 (by decide)
    finalReady := fun b hi _ => Residual.Branch.finalProtected hi (base_protected p original hf)
    fullCount := by simpa only [hm] using hc
    outputLength := by simp only [hm,width]; exact le_rfl
    timeBound := le_rfl }

 def ofRankResidualSpec (residual : Cmd 40 768) (original : Factor.Data)
    (hf : ∀i,Query.Protected i → i≠323 → initial.stacks i=original.stacks i)
    (hb : ∀i,i∈blankPorts → initial.stacks i=[])
    (hw : ∀i,(initial.stacks i).length ≤ W)
    (stepBudget stepWidth : ℕ)
    (hashes : List (SparseRow (Fin (Query.packingProblem q k hg).n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin (Query.packingProblem q k hg).n)))
    (hs : LeafBranchProgram.ResidualSpec LeafBranchProgram.Wide.fixedPorts residual
      (List.replicate (HighIncidenceProgram.Branches.trueCount q.forward.reverse) 1)
      (Residual.Branch.Invariant (base p)) stepBudget stepWidth
      (PreparedBranchCount.rankValue (NodeConcrete.planHigh (Query.packingProblem q k hg)) hashes marked clause)) :
    Marked.Wide.BranchContext residual (base p) (Query.ProtectedWork original)
      (PreparedBranchCount.fullCount hashes marked clause)
      (budget p stepBudget stepWidth) (width (q:=q) stepWidth) :=
  ofResidualSpec p residual original hf hb hw stepBudget stepWidth _ _ hs
    (PreparedBranchCount.query_rankSum_fullCount q k hg hashes marked clause)

 theorem ofRankResidualSpec_fields (residual : Cmd 40 768) (original : Factor.Data)
    (hf : ∀i,Query.Protected i → i≠323 → initial.stacks i=original.stacks i)
    (hb : ∀i,i∈blankPorts → initial.stacks i=[])
    (hw : ∀i,(initial.stacks i).length ≤ W)
    (stepBudget stepWidth : ℕ)
    (hashes : List (SparseRow (Fin (Query.packingProblem q k hg).n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin (Query.packingProblem q k hg).n)))
    (hs : LeafBranchProgram.ResidualSpec LeafBranchProgram.Wide.fixedPorts residual
      (List.replicate (HighIncidenceProgram.Branches.trueCount q.forward.reverse) 1)
      (Residual.Branch.Invariant (base p)) stepBudget stepWidth
      (PreparedBranchCount.rankValue (NodeConcrete.planHigh (Query.packingProblem q k hg)) hashes marked clause)) :
    let c := ofRankResidualSpec p residual original hf hb hw stepBudget stepWidth hashes marked clause hs
    c.stepBudget=stepBudget ∧ c.stepWidth=stepWidth ∧ c.referenceBound=Query.Width.incomingWidth p :=
  ⟨rfl,rfl,rfl⟩

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchContext

end OAI.Algorithms

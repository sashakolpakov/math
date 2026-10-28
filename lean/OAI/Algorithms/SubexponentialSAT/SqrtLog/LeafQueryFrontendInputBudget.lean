import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendCoreBound

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def Query.scopeCopyBudget (q : Query) : ℕ :=
  7*(Encoding.encodeList id q.clauses).length+5+
  (7*(HashScopeProgram.RawTable.inputBits q.width.length q.rows).length+5+
  (7*q.index.length+5+(7+5+(7*q.modulus.length+5+(7*q.width.length+5)))))

theorem scopeCopies_cost (q : Query) (a : Data) (ha : q.Ready a) :
    copiesCost scopeCopies a=q.scopeCopyBudget := by
  rcases ha with ⟨h700,h701,h705,h706,h707,h708,h709,hz,h338,h718,h719⟩
  simp [copiesCost,scopeCopies,copied_stack,Query.scopeCopyBudget,h700,h701,h705,h706,h707,h708]

def Query.highCapacity (q : Query) : ℕ :=
  (LeafStatisticsProgram.scopeBits q.scopeRows).length+BinaryArithmetic.toNat q.ambient+
    EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient)+q.ambient.length+
    (Asymptotic.L (BinaryArithmetic.toNat q.ambient)+1)+2

noncomputable def Query.coreInputBudget (q : Query) (k : ℕ) : ℕ :=
  let S := (LeafStatisticsProgram.scopeBits q.scopeRows).length
  let F := q.forward.length
  (q.scopeCopyBudget+21+HashScopeProgram.Complete.cost 1 0 q.width.length q.modulus
      q.clauses q.codes q.rows q.mark q.index+7*S) +
  (7*q.ambient.length+5+EarlyThreshold.runtimeBound q.ambient+
    (7*S+5+7*q.ambient.length+5+7*(Asymptotic.L (BinaryArithmetic.toNat q.ambient)+1)+5)+
    270000*q.highCapacity^3+17*F+14) +
  (7*S+5+7*F+5+LeafStatisticsProgram.bootBudget q.scopeRows q.forward+
    LeafStatisticsProgram.variableBudget q.scopeRows 0 q.forward+2+
    7*F+5+7*S+5+3+4+RecordPrograms.budget (LeafStatisticsProgram.Arity.cost q.forward)
      (q.scopeRows.map (Encoding.encodeList Encoding.encodeNat))+3*(totals q.scopeRows q.forward).uncovered+10) +
  q.numericCost k+LeafParametersProgram.Execute.runtimeBound (q.input k) (q.inputLengths k)+1

theorem coreBudget_le_input (q : Query) (k : ℕ) (a : Data) (ha : q.Ready a)
    (hn : 0 < BinaryArithmetic.toNat q.ambient) (tau : List Bool)
    (ht : BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient))
    (hl : tau.length ≤ Asymptotic.L (BinaryArithmetic.toNat q.ambient)+1) :
    coreBudget q k a tau (q.inputLengths k) ≤ q.coreInputBudget k := by
  have hc : HighIncidenceProgram.Prepare.inputCapacity q.scopeRows q.ambient tau ≤ q.highCapacity := by
    dsimp [HighIncidenceProgram.Prepare.inputCapacity,Query.highCapacity]
    rw [ht]
    exact Nat.add_le_add_right (Nat.add_le_add_left hl _) _
  have hh := (HighIncidenceProgram.Prepare.input_budget q.scopeRows q.ambient tau hn).trans
    (Nat.mul_le_mul_left 270000 (Nat.pow_le_pow_left hc 3))
  rw [coreBudget,Query.coreInputBudget,scopeCopies_cost q a ha]
  dsimp only [Query.numericCost,numericCost]
  omega

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms

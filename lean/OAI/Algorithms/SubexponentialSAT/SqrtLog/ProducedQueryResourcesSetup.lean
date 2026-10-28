import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupOuterCostInitialMajorant

namespace OAI.Algorithms

/-! Fixed proof-side setup constants selected from the actual native startup
and constructor theorem. These are not query inputs or a running-time oracle. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter Asymptotic
open scoped Topology
noncomputable section

 def setupC : ℕ := Classical.choose CodeSetupOuterCost.initial_resource_bound
 def setupD : ℕ := Classical.choose (Classical.choose_spec CodeSetupOuterCost.initial_resource_bound)
 def setupPadding : ℕ := Classical.choose (Classical.choose_spec
    (Classical.choose_spec CodeSetupOuterCost.initial_resource_bound))

 theorem setup_cost_bound : ∀ qi : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ m B W (records : List (List Bool)) (mword Bword qword Dword countWord : List Bool)
        (s : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B),
      0 < m → 0 < B → m ≤ n*B → B ≤ L n^qi →
      (Encoding.encodeList id records).length ≤ W →
      mword.length ≤ W+LeafOuterProgram.startBudget W records →
      Bword.length ≤ W+LeafOuterProgram.startBudget W records →
      countWord.length ≤ W+LeafOuterProgram.startBudget W records →
      qword.length ≤ mword.length+Bword.length+11 →
      Dword.length ≤ 4*mword.length+2*Bword.length+30 →
      LeafOuterProgram.startBudget W records+
        LeafOuterProgram.constructBudget (W+LeafOuterProgram.startBudget W records)
          mword Bword qword Dword countWord s Q ≤
        CodeSetupOuterCost.setupMajorant setupC setupD qi n*(W+1)^setupPadding :=
  Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec CodeSetupOuterCost.initial_resource_bound))

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms

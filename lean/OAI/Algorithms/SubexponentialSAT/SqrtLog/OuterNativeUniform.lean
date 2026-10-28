import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeRuntimeAt
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionSelectorCostJoin

namespace OAI.Algorithms

/-! One fixed coefficient/exponent pair covers both native query programs,
all reachable origins, all marked references, and every padded source. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT Filter ProducedQueryResources
open scoped Topology
noncomputable section

def queryCoefficient (k : ℕ) : ℝ :=
  runtimeCoefficient (markedCoefficient k) (markedExponent k)+
    runtimeCoefficient (acceptedCoefficient k) (acceptedExponent k)+1

def queryExponent (k qi : ℕ) : ℝ :=
  runtimeExponent k qi (markedExponent k)+runtimeExponent k qi (acceptedExponent k)

def queryDegree (k : ℕ) : ℕ := markedExponent k+acceptedExponent k

def uniformQueryLimit (k qi X n : ℕ) : ℕ :=
  Nat.ceil (Statement.runtimeBound (queryCoefficient k) (queryExponent k qi) (queryDegree k) X n)

 theorem queryCoefficient_ge_one (k : ℕ) : 1 ≤ queryCoefficient k := by
  have h1 := runtimeCoefficient_pos (markedCoefficient k) (markedExponent k)
  have h2 := runtimeCoefficient_pos (acceptedCoefficient k) (acceptedExponent k)
  unfold queryCoefficient
  linarith

 theorem queryExponent_nonneg (k qi : ℕ) : 0 ≤ queryExponent k qi := by
  have h1 := runtimeExponent_pos k qi (markedExponent k)
  have h2 := runtimeExponent_pos k qi (acceptedExponent k)
  unfold queryExponent
  linarith

 theorem eventually_uniform_runtime (k qi : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ B X, 0 < B → B ≤ Asymptotic.L n^qi →
      RuntimeAt n k B qi X (uniformQueryLimit k qi X n) := by
  filter_upwards [eventually_kernel_runtime k qi] with n hn
  intro B X hB hBL
  have common := (Execution.SelectorCost.common_queries
    (le_of_lt (runtimeCoefficient_pos (markedCoefficient k) (markedExponent k)))
    (le_of_lt (runtimeCoefficient_pos (acceptedCoefficient k) (acceptedExponent k)))
    (le_of_lt (runtimeExponent_pos k qi (markedExponent k)))
    (le_of_lt (runtimeExponent_pos k qi (acceptedExponent k)))
    (markedExponent k) (acceptedExponent k)).2.2
  constructor
  · intro q hv hqn ho hcount hsize
    refine ⟨(hn q B hv hqn ho hB hcount hBL).1,?_⟩
    unfold queryLimit
    rw [hqn]
    exact (common (queryBytes q) (queryBytes q) X n hsize hsize).1
  · intro q hv hqn ho hcount hsize
    refine ⟨(hn q B hv hqn ho hB hcount hBL).2,?_⟩
    unfold queryLimit
    rw [hqn]
    exact (common (queryBytes q) (queryBytes q) X n hsize hsize).2

end
end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms

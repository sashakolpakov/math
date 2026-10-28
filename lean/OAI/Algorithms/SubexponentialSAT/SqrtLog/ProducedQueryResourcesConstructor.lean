import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesScalars
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyAmbientLabels
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupOuterCostInitialMajorant

namespace OAI.Algorithms

/-! Numerical constructor for an actual query. Rank and maximum head size
are its two geometry arguments; ProducedQueryRank and LayoutProducedHeads
supply them from the actual packing. This module does not assert that an
arbitrary pair of natural numbers has those geometric bounds. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter Asymptotic LeafQueryFrontend CostAssembly
open scoped Topology

noncomputable section

/-- Uniform absolute coefficient-height envelope for the literal pulled
matrix. The ambient dimension is kept distinct from the free schedule. -/
def matrixHeight (q : Query) (k : ℕ) : ℕ :=
  2*(q.input k).occurrence*(8*layoutQ (q.input k).freeCount)^(
    2*layoutCutoff (q.input k).freeCount (q.input k).occurrence)

def make (q : Query) (k B labelRows headSize C d qi e : ℕ) : Resources where
  residual := (q.input k).freeCount
  clauses := q.clauses.length
  initialOccurrence := B
  localOccurrence := (q.input k).occurrence
  factors := (q.input k).factors
  branchVars := HighIncidenceProgram.Branches.trueCount (highMask q.scopeRows (ambient q))
  labelBase := 2*ambient q*matrixHeight q k+1
  labelRows := labelRows
  heads := layoutR (q.input k).freeCount
  headSize := headSize
  setup := CodeSetupOuterCost.setupMajorant C d qi (ambient q)
  bits := (ambient q+1)^e
  ordinary := (ambient q+1)^e

 theorem make_bits_pos (q : Query) (k B rows size C d qi e : ℕ) :
    1 ≤ (make q k B rows size C d qi e).bits := by
  exact Nat.one_le_pow _ _ (by omega)

 theorem make_heads_pos (q : Query) (k B rows size C d qi e : ℕ) :
    1 ≤ (make q k B rows size C d qi e).heads :=
  (by have := layoutR_ge_two (q.input k).freeCount; exact Nat.le_trans (by decide) this)

 theorem make_ordinary_bound (q : Query) (k B rows size C d qi e : ℕ)
    (hn : 1 ≤ ambient q) :
    (make q k B rows size C d qi e).bits*((make q k B rows size C d qi e).ordinary+1)^8 ≤
      (ambient q+1)^(9*e+8) := by
  let a := ambient q+1
  have ha : 2 ≤ a := by dsimp [a]; omega
  have hp : 1 ≤ a^e := Nat.one_le_pow _ _ (by omega)
  have h : a^e+1 ≤ a^(e+1) := by rw [pow_succ]; nlinarith
  change a^e*(a^e+1)^8 ≤ a^(9*e+8)
  calc
    _ ≤ a^e*(a^(e+1))^8 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
    _ = _ := by rw [←pow_mul,←pow_add]; congr 1; omega

 theorem heads_le_ambient (q : Query) (k : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k)) :
    layoutR (q.input k).freeCount ≤ ambient q+1 := by
  have hr := layoutR_ge_two (q.input k).freeCount
  have hq := hg.2.2.2.2.2.2.1
  have hbudget := hg.2.2.2.2.2.2.2.2.2
  change 16*layoutQ (q.input k).freeCount*(layoutR (q.input k).freeCount)^2 ≤ (q.input k).freeCount at hbudget
  change 2 ≤ layoutQ (q.input k).freeCount at hq
  have hfree := hg.2.1
  rw [input_ambient] at hfree
  nlinarith [Nat.mul_le_mul_right ((layoutR (q.input k).freeCount)^2) hq]

/-- Numerical join. The two explicit hypotheses are precisely the geometry
outputs proved from the produced packing; every other Bounds field is derived
here from actual selector/scan outputs and the fixed setup majorant. -/
theorem eventually_make_bounds (k qi C d e : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B rows size : ℕ), q.Valid → ambient q=n →
      Origin q k B → 0 < B → q.clauses.length ≤ n*B → B ≤ L n^qi →
      (16*(layoutR (q.input k).freeCount:ℝ)*(L (q.input k).freeCount:ℝ)^2*(rows:ℝ) ≤
        (q.input k).freeCount) →
      ((size:ℝ) ≤ 2*(n:ℝ)/layoutR (q.input k).freeCount) →
      Bounds qi (LeafScopeResourceBounds.resourceExponent qi+1) (9*e+8) n
        (make q k B rows size C d qi e) := by
  let ql := LeafScopeResourceBounds.resourceExponent qi+1
  filter_upwards [eventually_scan_bounds k qi,
    eventually_ambient_commonBase_log ql,
    CodeSetupOuterCost.setupMajorant_target C d qi,eventually_ge_atTop (1:ℕ)]
    with n hscan hbase hsetup hn q B rows size hv hqn o hB hc hBL hrows hsize
  have hs := hscan q B hv hqn o hB hc hBL
  have hb := hs.guard.2.2.2.1
  have hnfree : n ≤ 2*(q.input k).freeCount := by simpa only [hqn] using hs.residual.2
  refine ⟨?_,hc,hBL,hs.occurrence,?_,?_,by dsimp [make]; omega,hrows,?_,?_,hsize,?_,?_⟩
  · simpa only [make,hqn] using hs.residual
  · simpa only [make,hqn] using hs.factors
  · simpa only [make,hqn] using hs.branch
  · simpa only [make,matrixHeight,hqn] using
      hbase (q.input k).freeCount (q.input k).occurrence hnfree hb hs.occurrence
  · simpa only [make,hqn] using heads_le_ambient q k hs.guard
  · simpa only [make,hqn] using hsetup
  · simpa only [hqn] using make_ordinary_bound q k B rows size C d qi e (by omega)

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms

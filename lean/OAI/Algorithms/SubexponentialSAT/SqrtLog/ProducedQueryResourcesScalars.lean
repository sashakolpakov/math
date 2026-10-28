import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesOrigin
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramControllerResources
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramCrudeBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticResidual

namespace OAI.Algorithms

/-! Polynomial numerical dimensions of every actual large-input query.
These bounds do not include serialized bucket or sparse-dictionary buffers. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter Asymptotic LeafQueryFrontend
open scoped Topology

 theorem input_mass_le (q : Query) (k : ℕ) :
    (q.input k).incidences ≤ (q.input k).freeCount*(q.input k).occurrence := by
  have h := BucketProgram.Controller.Resources.native_rows_le q.scopeRows (ambient q) q.forward
  rw [PackingIncidenceInput.Stats.native_incidence_count] at h
  exact h

 theorem input_ambient (q : Query) (k : ℕ) : (q.input k).ambient=ambient q := rfl
 theorem input_width (q : Query) (k : ℕ) : (q.input k).width=k := rfl
 theorem input_clauses (q : Query) (k : ℕ) (hv : q.Valid) :
    (q.input k).clauses=q.clauses.length := hv.2.2.2.2.2.1

/-- This cap applies to scalar counts only. The free/incidence counts are
read from the native scan; no independent statistics are supplied. -/
structure SmallInputs (q : Query) (k n : ℕ) : Prop where
  free : (q.input k).freeCount ≤ n
  clauses : (q.input k).clauses ≤ n^2
  occurrence : (q.input k).occurrence ≤ n
  arity : (q.input k).arity ≤ n
  factors : (q.input k).factors ≤ n^2
  incidences : (q.input k).incidences ≤ n^2
  width : k ≤ n
  magnitude : LeafParametersProgram.magnitude (q.input k) ≤ n^4

 theorem small_inputs (k n qi ql : ℕ) (q : Query) (B : ℕ)
    (hv : q.Valid) (hn : ambient q=n) (hn16 : 16 ≤ n) (hk : k ≤ n)
    (hscan : ScanBounds q k ql) (hcl : q.clauses.length ≤ n*B) (hB : B ≤ L n^qi)
    (hLn : L n^qi ≤ n)
    (hLm : L (q.input k).freeCount^ql ≤ (q.input k).freeCount)
    (hsz : Nat.size q.clauses.length ≤ n) : SmallInputs q k n := by
  have hf : (q.input k).freeCount ≤ n := by simpa only [hn] using hscan.residual.1
  have ho : (q.input k).occurrence ≤ n := (hscan.occurrence.trans hLm).trans hf
  have ha : (q.input k).arity ≤ n := (hscan.arity.trans hLm).trans hf
  have hc : (q.input k).clauses ≤ n^2 := by
    rw [input_clauses q k hv]
    exact hcl.trans (by simpa only [pow_two] using Nat.mul_le_mul_left n (hB.trans hLn))
  have hfac : (q.input k).factors ≤ n^2 := by
    have hh := hscan.factors
    rw [hn] at hh
    unfold HashSelect.loopCap at hh
    nlinarith
  have hmass : (q.input k).incidences ≤ n^2 :=
    (input_mass_le q k).trans (by simpa only [pow_two] using Nat.mul_le_mul hf ho)
  refine ⟨hf,hc,ho,ha,hfac,hmass,hk,?_⟩
  have hn2 : n ≤ n^2 := by nlinarith
  have hm : LeafParametersProgram.magnitude (q.input k) ≤ 8*n^2+16 := by
    unfold LeafParametersProgram.magnitude
    rw [input_ambient,input_width,hn]
    omega
  exact hm.trans (by nlinarith [sq_nonneg (n*n)])

/-- All scalar input fields are bounded together, with one cutoff depending
only on k and the initial occurrence exponent. -/
theorem eventually_small_inputs (k qi : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B : ℕ), q.Valid → ambient q=n →
      Origin q k B → 0 < B → q.clauses.length ≤ n*B → B ≤ L n^qi →
      ScanBounds q k (LeafScopeResourceBounds.resourceExponent qi+1) ∧ SmallInputs q k n := by
  let ql := LeafScopeResourceBounds.resourceExponent qi+1
  filter_upwards [eventually_scan_bounds k qi, CostAssembly.eventually_sparse_parameter_bounds qi,
    eventually_L_power_le_n qi (by norm_num : (0:ℝ) < 1),
    eventually_uniform_half (eventually_L_power_le_n ql (by norm_num : (0:ℝ) < 1)),
    eventually_ge_atTop (max 16 k)] with n hscan hpar hLn hLm hn q B hv hqn o hB hc hBL
  have hs := hscan q B hv hqn o hB hc hBL
  have hm : n ≤ 2*(q.input k).freeCount := by simpa only [hqn] using hs.residual.2
  have hlm : L (q.input k).freeCount^ql ≤ (q.input k).freeCount := by
    exact_mod_cast (by simpa using hLm (q.input k).freeCount hm :
      (L (q.input k).freeCount:ℝ)^ql ≤ (q.input k).freeCount)
  have hln : L n^qi ≤ n := by exact_mod_cast (by simpa using hLn : (L n:ℝ)^qi ≤ n)
  exact ⟨hs,small_inputs k n qi ql q B hv hqn (by omega) (by omega) hs hc hBL hln hlm
    (hpar q.clauses.length B hc hBL).1⟩

end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms

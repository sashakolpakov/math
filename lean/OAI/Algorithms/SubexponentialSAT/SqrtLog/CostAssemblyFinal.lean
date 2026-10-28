import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyCodeParameters
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyResidual
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyResidualEnumeration
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyBuckets
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyClosure

namespace OAI.Algorithms

/-! One closed cost expression with actual jet order, hash candidate count,
high-incidence branch count, and joint-signature/head enumeration. The two
remaining algorithmic interfaces are setup work and ordinary primitive work. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open Asymptotic

structure Resources where
  residual : ℕ
  clauses : ℕ
  initialOccurrence : ℕ
  localOccurrence : ℕ
  factors : ℕ
  branchVars : ℕ
  labelBase : ℕ
  /-- Rank used only to bound the number of attained signatures.  It need
  not be the number of rows stored or processed by the native program. -/
  labelRows : ℕ
  heads : ℕ
  headSize : ℕ
  setup : ℕ
  /-- Primitive coefficient/key costs; these use the actual retained rows. -/
  bits : ℕ
  /-- Includes actual matrix rows and payload dimensions, even when they
  exceed the rank parameter `labelRows`. -/
  ordinary : ℕ

def jetNumerator (n : ℕ) (p : Resources) : ℕ :=
  2*p.factors+3*(LeafParametersProgram.precision n p.clauses-1)+1

def jetOrder (k n : ℕ) (p : Resources) : ℕ :=
  k*layoutCutoff p.residual p.localOccurrence*jetNumerator n p/layoutQ p.residual+1

def assembledWork (k n : ℕ) (p : Resources) : ℕ :=
  sparseWork n (jetOrder k n p) p.setup
    (hashCalls n p.clauses (SparseCode.distanceDenom p.clauses p.initialOccurrence))
    (2^p.branchVars) (enumerationWork p.labelBase p.labelRows p.heads p.headSize)
    p.bits p.ordinary

/-- All fixed-k numerical losses are displayed in this coefficient. -/
noncomputable def exponentConstant (k q : ℕ) : ℝ :=
  707+4*(384*(((k*30*(256*(28*q+312)):ℕ):ℝ)+1)+1)

/-- A sequence-specific global estimate: its constant may depend on `p`.
The uniform solver interface is `assembledWork_uniform_cutoff` in
`CostAssemblyUniform`, which handles every resource record above one cutoff. -/
theorem assembledWork_target (p : ℕ → Resources) (k qi ql d : ℕ)
    (hres : ∀ᶠ n:ℕ in atTop, (p n).residual ≤ n ∧ n ≤ 2*(p n).residual)
    (hclauses : ∀ᶠ n:ℕ in atTop, (p n).clauses ≤ n*(p n).initialOccurrence)
    (hini : ∀ᶠ n:ℕ in atTop, (p n).initialOccurrence ≤ L n^qi)
    (hloc : ∀ᶠ n:ℕ in atTop, (p n).localOccurrence ≤ L (p n).residual^ql)
    (hfactors : ∀ᶠ n:ℕ in atTop,
      (p n).factors ≤ 3*n+HashSelect.loopCap n (p n).clauses+1)
    (hbranch : ∀ᶠ n:ℕ in atTop,
      ((p n).branchVars:ℝ) ≤ (n:ℝ)/Real.sqrt (L n:ℝ))
    (hbase : ∀ᶠ n:ℕ in atTop, 0 < (p n).labelBase)
    (hrows : ∀ᶠ n:ℕ in atTop,
      16*(layoutR (p n).residual:ℝ)*(L (p n).residual:ℝ)^2*((p n).labelRows:ℝ) ≤ (p n).residual)
    (hheight : ∀ᶠ n:ℕ in atTop,
      Real.log ((p n).labelBase:ℝ) ≤ 4*(L (p n).residual:ℝ)^2)
    (hheads : ∀ᶠ n:ℕ in atTop, (p n).heads ≤ n+1)
    (hsize : ∀ᶠ n:ℕ in atTop,
      ((p n).headSize:ℝ) ≤ 2*(n:ℝ)/layoutR (p n).residual)
    (hsetup : ∀ᶠ n:ℕ in atTop, ((p n).setup:ℝ) ≤ (2:ℝ)^Statement.runtimeScale n)
    (hbits : ∀ᶠ n:ℕ in atTop, (p n).bits*((p n).ordinary+1)^8 ≤ (n+1)^d) :
    ∃K:ℝ, 0 < K ∧ ∀n,
      (assembledWork k n (p n):ℝ) ≤ K*(2:ℝ)^(exponentConstant k ql*Statement.runtimeScale n) := by
  let C : ℝ := ((k*30*(256*(28*ql+312)):ℕ):ℝ)+1
  have hC : 1 ≤ C := by
    dsimp [C]
    have : (0:ℝ) ≤ (k*30*(256*(28*ql+312)):ℕ) := by positivity
    linarith
  have hT := eventually_linear_jet_envelope (fun n => (p n).clauses)
    (fun n => (p n).initialOccurrence) (fun n => (p n).factors) qi hclauses hini hfactors
  have hJ := eventually_residual_jet_functions (fun n => (p n).residual)
    (fun n => (p n).localOccurrence) (fun n => jetNumerator n (p n))
    k 30 ql hres hloc hT
  have hSupport := eventually_support_target (fun n => jetOrder k n (p n)) hC hJ
  have hCalls := eventually_constructed_hashCalls (fun n => (p n).clauses)
    (fun n => (p n).initialOccurrence) qi hclauses hini
  have hPoly := eventually_polynomial_target d
  have hExp : 0 ≤ exponentConstant k ql := by unfold exponentConstant; positivity
  have hev : ∀ᶠ n:ℕ in atTop,
      (assembledWork k n (p n):ℝ)/17 ≤ (2:ℝ)^(exponentConstant k ql*Statement.runtimeScale n) := by
    filter_upwards [hSupport,hCalls,hPoly,hres,hbranch,hbase,hrows,hheight,hheads,hsize,
      hsetup,hbits,eventually_residual_enumeration_ambient_bound]
      with n hs hc hp hr hb hba hro hhe hhd hsz hse hbi hen
    have hEnum := hen (p n).residual (p n).labelBase (p n).labelRows (p n).heads
      (p n).headSize hr.1 hr.2 hba hro hhe hhd hsz
    have hBranch : ((2^(p n).branchVars:ℕ):ℝ) ≤ (2:ℝ)^(64*Statement.runtimeScale n) := by
      push_cast
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (hb.trans (high_branch_exponent_le n))
    have hOrd : ((p n).bits:ℝ)*((p n).ordinary+1:ℕ)^8 ≤ (2:ℝ)^Statement.runtimeScale n := by
      exact (show ((p n).bits:ℝ)*((p n).ordinary+1:ℕ)^8 ≤ ((n+1)^d:ℕ) by exact_mod_cast hbi).trans hp
    have hh := sparseWork_le n (jetOrder k n (p n)) (p n).setup
      (hashCalls n (p n).clauses (SparseCode.distanceDenom (p n).clauses (p n).initialOccurrence))
      (2^(p n).branchVars) (enumerationWork (p n).labelBase (p n).labelRows (p n).heads (p n).headSize)
      (p n).bits (p n).ordinary (Statement.runtimeScale_nonneg n)
      (by norm_num : (0:ℝ) ≤ 641) (by norm_num : (0:ℝ) ≤ 64)
      (show 0 ≤ 384*C+1 by linarith) hse hc hBranch hEnum hOrd hs
    change (assembledWork k n (p n):ℝ) ≤ _ at hh
    have heq : 2+(64:ℝ)+641+4*(384*C+1)=exponentConstant k ql := by
      unfold exponentConstant C
      ring
    rw [heq] at hh
    linarith
  obtain ⟨K,hK,hbound⟩ := finite_prefix_absorption _ hExp hev
  refine ⟨17*K,by positivity,?_⟩
  intro n
  have hh := hbound n
  nlinarith

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms

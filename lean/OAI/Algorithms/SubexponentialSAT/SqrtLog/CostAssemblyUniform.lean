import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyFinal

namespace OAI.Algorithms

/-! Uniform bounds over every input at a fixed size.  The cutoff depends only
on fixed numerical exponents, never on a chosen sequence of formulas. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly
open Filter
open scoped Topology
open Asymptotic

theorem eventually_support_bound {C : ℝ} (hC : 1 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ J : ℕ, (J : ℝ) ≤ entropyCutoff n C →
      (SupportProgram.count n J : ℝ) ≤
      (2 : ℝ)^((384 * C + 1) * Statement.runtimeScale n) := by
  have hCpos : 0 < C := by linarith
  have hsmall := eventually_w_power_le_L 2 (sq_pos_of_pos hCpos)
  have hpoly := eventually_polylog_le_target 1 (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hsmall, hpoly, eventually_ge_atTop 1] with n hnsmall hnpoly hn J hJ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hw : (1 : ℝ) ≤ w n := by exact_mod_cast w_pos n
  have hL : (0 : ℝ) < L n := by exact_mod_cast L_pos n
  have hr : 0 < Real.sqrt (L n : ℝ) := Real.sqrt_pos.2 hL
  have hcw : C * (w n : ℝ) ≤ Real.sqrt (L n : ℝ) := by
    apply (Real.le_sqrt (by positivity) hL.le).2
    nlinarith [hnsmall]
  have hu : 0 < entropyCutoff n C := by unfold entropyCutoff; positivity
  have hun : entropyCutoff n C ≤ n := by
    unfold entropyCutoff
    apply (div_le_iff₀ hr).2
    nlinarith
  have hlo : (n : ℝ) / Real.sqrt (L n : ℝ) ≤ entropyCutoff n C := by
    unfold entropyCutoff
    apply div_le_div_of_nonneg_right _ hr.le
    have hc := mul_le_mul hC hw (by norm_num : (0 : ℝ) ≤ 1) hCpos.le
    nlinarith
  have hmain := support_le_entropy n J hu hun hJ hlo
  have hcost : 6 * entropyCutoff n C * w n ≤
      384 * C * Statement.runtimeScale n := by
    have hh := mul_le_mul_of_nonneg_left (weighted_scale_le_target n) (show 0 ≤ 6*C by positivity)
    unfold entropyCutoff
    convert hh using 1 <;> ring
  have hJn : (J : ℝ) ≤ n := hJ.trans hun
  have hnexp : (n : ℝ) ≤ (2 : ℝ)^Statement.runtimeScale n := by
    have hlog : logSize n ≤ Statement.runtimeScale n := by simpa using hnpoly
    calc
      (n : ℝ) ≤ (n : ℝ) + 16 := by linarith
      _ = (2 : ℝ)^logSize n := by
        symm
        exact Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
  calc
    (SupportProgram.count n J : ℝ) ≤
        (J : ℝ) * (2 : ℝ)^(6 * entropyCutoff n C * w n) := hmain
    _ ≤ (2 : ℝ)^Statement.runtimeScale n *
        (2 : ℝ)^(384*C*Statement.runtimeScale n) := by
      exact mul_le_mul (hJn.trans hnexp)
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hcost)
        (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring


theorem eventually_sparse_parameter_bounds (q : ℕ) :
    ∀ᶠ n:ℕ in atTop, ∀m B:ℕ, m ≤ n*B → B ≤ L n^q →
      Nat.size m ≤ n ∧ m ≤ n^2 ∧ SparseCode.distanceDenom m B ≤ L n^(2*q+3) := by
  have hs := eventually_L_power_le_n 1 (show (0:ℝ) < (q:ℝ)+2 by positivity)
  have hb := eventually_L_power_le_n q (by norm_num : (0:ℝ) < 1)
  have hc := eventually_absorb_L_coefficient
    (fun n => 20000*(q+2)^2*L n^(2*q+2)) (20000*(q+2)^2) (2*q+2)
    (Filter.Eventually.of_forall (fun _ => le_rfl))
  filter_upwards [hs,hb,hc] with n hsn hbn hcn m B hm hB
  have hsize := sparse_clause_size_le n m B q hm hB
  have hL : 1 ≤ L n := L_pos n
  have hsn' : (q+2)*L n ≤ n := by
    exact_mod_cast (by simpa using hsn : ((q:ℝ)+2)*(L n:ℝ) ≤ n)
  have hbn' : L n^q ≤ n := by exact_mod_cast (by simpa using hbn : (L n:ℝ)^q ≤ n)
  refine ⟨by nlinarith,by nlinarith,?_⟩
  exact (code_distanceDenom_le n m B q hm hB).trans hcn

theorem eventually_hashCalls_bound (q : ℕ) :
    ∀ᶠ n:ℕ in atTop, ∀m B:ℕ, m ≤ n*B → B ≤ L n^q →
      (hashCalls n m (SparseCode.distanceDenom m B):ℝ) ≤
        (2:ℝ)^Statement.runtimeScale n := by
  have hdeg : ∀ᶠ n:ℕ in atTop,
      ((3*L n^(2*q+3)+7:ℕ):ℝ) ≤ 10*(L n:ℝ)^(2*q+3) := by
    filter_upwards [] with n
    have h : 1 ≤ L n^(2*q+3) := Nat.one_le_pow _ _ (L_pos n)
    have hh : 3*L n^(2*q+3)+7 ≤ 10*L n^(2*q+3) := by omega
    exact_mod_cast hh
  have hpow := eventually_polylog_degree_target (fun n => 3*L n^(2*q+3)+7)
    (2*q+3) (by norm_num : (0:ℝ) < 10) hdeg
  filter_upwards [eventually_sparse_parameter_bounds q,hpow,eventually_ge_atTop 1]
    with n hpar hpow hn m B hm hB
  obtain ⟨hsize,hm2,hP⟩ := hpar m B hm hB
  have hc := hashCalls_le n m (SparseCode.distanceDenom m B) hn hm2 hsize
  have hc' : hashCalls n m (SparseCode.distanceDenom m B) ≤
      (n+1)^(3*L n^(2*q+3)+7) :=
    hc.trans (Nat.pow_le_pow_right (by omega) (by omega))
  exact (show (hashCalls n m (SparseCode.distanceDenom m B):ℝ) ≤
    ((n+1)^(3*L n^(2*q+3)+7):ℕ) by exact_mod_cast hc').trans hpow

/-- Include up to n additional neutral factors in the literal jet-order
parameter.  They need not be removed from that parameter by the evaluator. -/
theorem linear_jet_envelope_with_neutrals (n m factors : ℕ) (hn : 2 ≤ n)
    (hm : Nat.size m ≤ n) (hf : factors ≤ 4*n+HashSelect.loopCap n m+2) :
    2*factors+3*(LeafParametersProgram.precision n m-1)+1 ≤ 30*n := by
  unfold HashSelect.loopCap at hf
  unfold LeafParametersProgram.precision
  omega

/-- All input-dependent premises are pointwise.  None is hidden in the
threshold used by `eventually_assembledWork_bound`. -/
structure Bounds (qi ql d n : ℕ) (p : Resources) : Prop where
  residual : p.residual ≤ n ∧ n ≤ 2*p.residual
  clauses : p.clauses ≤ n*p.initialOccurrence
  initial : p.initialOccurrence ≤ L n^qi
  occurrence : p.localOccurrence ≤ L p.residual^ql
  factors : p.factors ≤ 4*n+HashSelect.loopCap n p.clauses+2
  branch : (p.branchVars:ℝ) ≤ (n:ℝ)/Real.sqrt (L n:ℝ)
  base : 0 < p.labelBase
  rows : 16*(layoutR p.residual:ℝ)*(L p.residual:ℝ)^2*(p.labelRows:ℝ) ≤ p.residual
  height : Real.log (p.labelBase:ℝ) ≤ 4*(L p.residual:ℝ)^2
  heads : p.heads ≤ n+1
  headSize : (p.headSize:ℝ) ≤ 2*(n:ℝ)/layoutR p.residual
  setup : (p.setup:ℝ) ≤ (2:ℝ)^Statement.runtimeScale n
  ordinary : p.bits*(p.ordinary+1)^8 ≤ (n+1)^d

/-- A single threshold works for every resource record, hence every formula
and every retained-half branch satisfying the displayed numerical estimates.
Small inputs are deliberately left to the actual finite-fallback machine. -/
theorem eventually_assembledWork_bound (k qi ql d : ℕ) :
    ∀ᶠ n:ℕ in atTop, ∀p:Resources, Bounds qi ql d n p →
      (assembledWork k n p:ℝ) ≤
        17*(2:ℝ)^(exponentConstant k ql*Statement.runtimeScale n) := by
  let C : ℝ := ((k*30*(256*(28*ql+312)):ℕ):ℝ)+1
  have hC : 1 ≤ C := by
    dsimp [C]
    have : (0:ℝ) ≤ (k*30*(256*(28*ql+312)):ℕ) := by positivity
    linarith
  filter_upwards [eventually_support_bound hC,eventually_hashCalls_bound qi,
    eventually_sparse_parameter_bounds qi,eventually_residual_jet_bound k 30 ql,
    eventually_residual_enumeration_ambient_bound,eventually_polynomial_target d,
    eventually_ge_atTop 2] with n hsup hcalls hpar hjet henum hpoly hn p hp
  have hsz := (hpar p.clauses p.initialOccurrence hp.clauses hp.initial).1
  have hT : jetNumerator n p ≤ 30*n :=
    linear_jet_envelope_with_neutrals n p.clauses p.factors hn hsz hp.factors
  have hJ : (jetOrder k n p:ℝ) ≤ entropyCutoff n C :=
    hjet p.residual p.localOccurrence (jetNumerator n p)
      hp.residual.1 hp.residual.2 hp.occurrence hT
  have hSupport := hsup (jetOrder k n p) hJ
  have hCalls := hcalls p.clauses p.initialOccurrence hp.clauses hp.initial
  have hEnum := henum p.residual p.labelBase p.labelRows p.heads p.headSize
    hp.residual.1 hp.residual.2 hp.base hp.rows hp.height hp.heads hp.headSize
  have hBranch : ((2^p.branchVars:ℕ):ℝ) ≤ (2:ℝ)^(64*Statement.runtimeScale n) := by
    push_cast
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (hp.branch.trans (high_branch_exponent_le n))
  have hOrd : (p.bits:ℝ)*(p.ordinary+1:ℕ)^8 ≤ (2:ℝ)^Statement.runtimeScale n := by
    exact (show (p.bits:ℝ)*(p.ordinary+1:ℕ)^8 ≤ ((n+1)^d:ℕ) by
      exact_mod_cast hp.ordinary).trans hpoly
  have h := sparseWork_le n (jetOrder k n p) p.setup
    (hashCalls n p.clauses (SparseCode.distanceDenom p.clauses p.initialOccurrence))
    (2^p.branchVars) (enumerationWork p.labelBase p.labelRows p.heads p.headSize)
    p.bits p.ordinary (Statement.runtimeScale_nonneg n)
    (by norm_num : (0:ℝ) ≤ 641) (by norm_num : (0:ℝ) ≤ 64)
    (show 0 ≤ 384*C+1 by linarith) hp.setup hCalls hBranch hEnum hOrd hSupport
  change (assembledWork k n p:ℝ) ≤ _ at h
  have heq : 2+(64:ℝ)+641+4*(384*C+1)=exponentConstant k ql := by
    unfold exponentConstant C
    ring
  rw [heq] at h
  exact h

theorem assembledWork_uniform_cutoff (k qi ql d : ℕ) :
    ∃N:ℕ, ∀n ≥ N, ∀p:Resources, Bounds qi ql d n p →
      (assembledWork k n p:ℝ) ≤
        17*(2:ℝ)^(exponentConstant k ql*Statement.runtimeScale n) := by
  exact Filter.eventually_atTop.mp (eventually_assembledWork_bound k qi ql d)

/-- Explicit closure for native algorithms that are polynomial in the
assembled counter.  In particular quadratic bucket grouping pays for its
second factor of `2^headSize` here, never inside a polynomial in n. -/
def nativeEnvelope (k n power ordinaryPower : ℕ) (p : Resources) : ℕ :=
  (n+1)^ordinaryPower*(assembledWork k n p+1)^power

theorem eventually_nativeEnvelope_bound (k qi ql d power ordinaryPower : ℕ) :
    ∀ᶠ n:ℕ in atTop, ∀p:Resources, Bounds qi ql d n p →
      (nativeEnvelope k n power ordinaryPower p:ℝ) ≤
        (18:ℝ)^power*(2:ℝ)^((1+(power:ℝ)*exponentConstant k ql)*Statement.runtimeScale n) := by
  filter_upwards [eventually_assembledWork_bound k qi ql d,
    eventually_polynomial_target ordinaryPower] with n hwork hpoly p hp
  have hw := hwork p hp
  have hA : 0 ≤ exponentConstant k ql := by unfold exponentConstant; positivity
  have hone : (1:ℝ) ≤ (2:ℝ)^(exponentConstant k ql*Statement.runtimeScale n) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hA (Statement.runtimeScale_nonneg n))
  have hw' : (assembledWork k n p:ℝ)+1 ≤
      18*(2:ℝ)^(exponentConstant k ql*Statement.runtimeScale n) := by linarith
  have hpow : ((assembledWork k n p:ℝ)+1)^power ≤
      (18:ℝ)^power*(2:ℝ)^((power:ℝ)*exponentConstant k ql*Statement.runtimeScale n) := by
    calc
      _ ≤ (18*(2:ℝ)^(exponentConstant k ql*Statement.runtimeScale n))^power := by gcongr
      _ = _ := by
        rw [mul_pow,← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
        congr 2
        ring
  unfold nativeEnvelope
  push_cast at hpoly
  push_cast
  calc
    _ ≤ (2:ℝ)^Statement.runtimeScale n*
        ((18:ℝ)^power*(2:ℝ)^((power:ℝ)*exponentConstant k ql*Statement.runtimeScale n)) := by
      exact mul_le_mul hpoly hpow (by positivity) (by positivity)
    _ = _ := by
      rw [show (2:ℝ)^Statement.runtimeScale n*
          ((18:ℝ)^power*(2:ℝ)^((power:ℝ)*exponentConstant k ql*Statement.runtimeScale n)) =
          (18:ℝ)^power*((2:ℝ)^Statement.runtimeScale n*
            (2:ℝ)^((power:ℝ)*exponentConstant k ql*Statement.runtimeScale n)) by ring,
        ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 2
      ring

theorem nativeEnvelope_uniform_cutoff (k qi ql d power ordinaryPower : ℕ) :
    ∃N:ℕ, ∀n ≥ N, ∀p:Resources, Bounds qi ql d n p →
      (nativeEnvelope k n power ordinaryPower p:ℝ) ≤
        (18:ℝ)^power*(2:ℝ)^((1+(power:ℝ)*exponentConstant k ql)*Statement.runtimeScale n) := by
  exact Filter.eventually_atTop.mp
    (eventually_nativeEnvelope_bound k qi ql d power ordinaryPower)

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms

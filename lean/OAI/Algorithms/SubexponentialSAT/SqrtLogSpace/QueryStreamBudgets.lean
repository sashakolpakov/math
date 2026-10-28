import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ResourceBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionRuntime

/-! Fixed polynomial time envelopes for the actual conditioned stream. The
same original assembled resource pays the support/tuple work; all remaining
scalars and retained words enter only fixed polynomial coefficients. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets
open SqrtLog SubexpLiftRing SubexpQuarticRing
open CostAssembly.Polynomial QueryStreamCorrect

private def finishEnvelope (X : ℕ) : ℕ :=
  29*X+27+(41*(2*X+3)+30000*(X+2*X+X+X+X+1)^6+1)+
    6*(X+X*(X*(2*X)))+9+4*X+10

private def reconstructionCoefficient : ℕ :=
  2400*(ReconstructionProgram.Native.costConstant+1)^4+
    5*LeafProgram.Count.Prepare.ports.length+39628

private def scalarEnvelope (X : ℕ) : ℕ :=
  18*X+65*X+67+23*X+
    X*(20000*(X+1)^4+300*(X+1)+X+10+finishEnvelope X+1)+32+
    reconstructionCoefficient*(2*X+1)^96

private theorem finishEnvelope_polynomial : Ordinary finishEnvelope := by
  have htwo := ordinary_mul (ordinary_const 2) ordinary_id
  have hbase := ordinary_add (ordinary_add (ordinary_add (ordinary_add
    (ordinary_add ordinary_id htwo) ordinary_id) ordinary_id) ordinary_id) (ordinary_const 1)
  have hmain := ordinary_add (ordinary_add
    (ordinary_mul (ordinary_const 41) (ordinary_add htwo (ordinary_const 3)))
    (ordinary_mul (ordinary_const 30000) (ordinary_pow hbase 6))) (ordinary_const 1)
  have hcubic := ordinary_mul (ordinary_const 6)
    (ordinary_add ordinary_id (ordinary_mul ordinary_id (ordinary_mul ordinary_id htwo)))
  exact ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add
    (ordinary_add (ordinary_mul (ordinary_const 29) ordinary_id) (ordinary_const 27))
    hmain) hcubic) (ordinary_const 9))
    (ordinary_mul (ordinary_const 4) ordinary_id)) (ordinary_const 10)

private theorem scalarPolynomial (R : ℕ) : Ordinary (fun X =>
    18*X+65*X+67+23*X+
      X*(20000*(X+1)^4+300*(X+1)+X+10+finishEnvelope X+1)+32+
      R*(2*X+1)^96) := by
  have hbase := ordinary_add ordinary_id (ordinary_const 1)
  have hprepare := ordinary_add (ordinary_mul (ordinary_const 20000) (ordinary_pow hbase 4))
    (ordinary_mul (ordinary_const 300) hbase)
  have hnode := ordinary_add (ordinary_add (ordinary_add
    (ordinary_add hprepare ordinary_id) (ordinary_const 10)) finishEnvelope_polynomial)
    (ordinary_const 1)
  have hprefix := ordinary_add (ordinary_add (ordinary_add
    (ordinary_mul (ordinary_const 18) ordinary_id)
    (ordinary_mul (ordinary_const 65) ordinary_id)) (ordinary_const 67))
    (ordinary_mul (ordinary_const 23) ordinary_id)
  have hrec := ordinary_mul (ordinary_const R) (ordinary_pow
    (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 1)) 96)
  exact ordinary_add (ordinary_add (ordinary_add hprefix
    (ordinary_mul ordinary_id hnode)) (ordinary_const 32)) hrec

private theorem scalarEnvelope_polynomial : Ordinary scalarEnvelope :=
  scalarPolynomial reconstructionCoefficient

private theorem finish_le (n t d J A X : ℕ)
    (hn : n ≤ X) (ht : t ≤ X) (hd : d ≤ X) (hJ : J ≤ X)
    (hF : QueryHeadBudgets.compact A ≤ X) :
    finishBudget n t d J A ≤ finishEnvelope X := by
  have h := QueryNodeFinish.budget_polynomial n (baseWidth 3 t) d t J
    (QueryHeadBudgets.compact A)
  apply h.trans
  simp only [RingProgram.ternary_baseWidth]
  unfold finishEnvelope
  gcongr

private theorem budget_le_scalar (n t d Q J A S work X : ℕ)
    (hn : n ≤ X) (ht : t ≤ X) (hd : d ≤ X) (hQ : Q ≤ X) (hJ : J ≤ X)
    (hS : S ≤ X) (hF : QueryHeadBudgets.compact A ≤ X)
    (hpair : StreamedQueryMeasuredCost.pairCoefficient A ≤ X) :
    budget n t d Q J A S work ≤ scalarEnvelope X*(work+1)^2 := by
  have hfinish := finish_le n t d J A X hn ht hd hJ hF
  have hrec := QueryReconstruction.budget_polynomial (QueryHeadBudgets.compact A) S
  have hrec' : QueryReconstruction.budget (QueryHeadBudgets.compact A) S ≤
      reconstructionCoefficient*(2*X+1)^96 := hrec.trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 96))
  have hraw : budget n t d Q J A S work ≤
      18*X+65*X+67+23*X+
      X*(20000*(X+1)^4+300*(X+1)+X*work^2+10+finishEnvelope X+1)+32+
      reconstructionCoefficient*(2*X+1)^96 := by
    unfold budget nodeBudget prepareBudget
    gcongr
  let rest := 18*X+65*X+67+23*X+
    X*(20000*(X+1)^4+300*(X+1)+10+finishEnvelope X+1)+32+
    reconstructionCoefficient*(2*X+1)^96
  have hone : 1 ≤ (work+1)^2 := Nat.one_le_pow' _ _
  have hpow : work^2 ≤ (work+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hrest := Nat.mul_le_mul_left rest hone
  have hp := Nat.mul_le_mul_left (X*X) hpow
  apply hraw.trans
  change _ ≤ scalarEnvelope X*(work+1)^2
  unfold scalarEnvelope
  dsimp [rest] at hrest
  nlinarith only [hrest,hp]

/-- All coefficients and degrees precede every query, node and physical cap.
The exponential term is exactly the square of the same original work value. -/
theorem budget_polynomial : ∃ C e : ℕ, ∀ n t d Q J A S work U : ℕ,
    n ≤ U → t ≤ U → d ≤ U → Q ≤ U → J ≤ U → A ≤ U → S ≤ U →
    budget n t d Q J A S work ≤ C*(U+1)^e*(work+1)^2 := by
  obtain ⟨Cc,dc,hc⟩ := QueryHeadBudgets.caps_polynomial
  obtain ⟨Cp,dp,hp⟩ := StreamedQueryMeasuredCost.pairCoefficient_polynomial
  obtain ⟨Ce,de,he⟩ := scalarEnvelope_polynomial
  let degree := dc+dp+1
  let coefficient := Cc+Cp+1
  refine ⟨Ce*(coefficient+1)^de,degree*de,?_⟩
  intro n t d Q J A S work U hn ht hd hQ hJ hA hS
  let X := coefficient*(U+1)^degree
  have hbase : 1 ≤ U+1 := by omega
  have hlinear : U ≤ X := by
    have h := Nat.le_self_pow (show degree ≠ 0 by dsimp [degree]; omega) (U+1)
    have hm := Nat.le_mul_of_pos_left ((U+1)^degree)
      (show 0 < coefficient by dsimp [coefficient]; omega)
    omega
  have hcompact : QueryHeadBudgets.compact A ≤ X := by
    have h0 := (hc A).1
    have hpow : (A+1)^dc ≤ (U+1)^degree :=
      (Nat.pow_le_pow_left (by omega) dc).trans (Nat.pow_le_pow_right hbase (by dsimp [degree]; omega))
    exact h0.trans (Nat.mul_le_mul (by dsimp [coefficient]; omega) hpow)
  have hpair : StreamedQueryMeasuredCost.pairCoefficient A ≤ X := by
    have hpow : (A+1)^dp ≤ (U+1)^degree :=
      (Nat.pow_le_pow_left (by omega) dp).trans (Nat.pow_le_pow_right hbase (by dsimp [degree]; omega))
    exact (hp A).trans (Nat.mul_le_mul (by dsimp [coefficient]; omega) hpow)
  have h := budget_le_scalar n t d Q J A S work X
    (hn.trans hlinear) (ht.trans hlinear) (hd.trans hlinear) (hQ.trans hlinear)
    (hJ.trans hlinear) (hS.trans hlinear) hcompact hpair
  have hs := polynomialBudget_substitute (scalarEnvelope X) X U Ce de coefficient degree
    (he X) le_rfl
  exact h.trans (Nat.mul_le_mul_right _ hs)

/-- Fixed-power comparison in the original work counter and a physical cap. -/
theorem budget_fixed_power : ∃ C e : ℕ, ∀ n t d Q J A S work U : ℕ,
    n ≤ U → t ≤ U → d ≤ U → Q ≤ U → J ≤ U → A ≤ U → S ≤ U →
    budget n t d Q J A S work ≤ C*(work+U+1)^e := by
  obtain ⟨C,e,h⟩ := budget_polynomial
  refine ⟨C,e+2,?_⟩
  intro n t d Q J A S work U hn ht hd hQ hJ hA hS
  calc
    _ ≤ C*(U+1)^e*(work+1)^2 := h n t d Q J A S work U hn ht hd hQ hJ hA hS
    _ ≤ C*(work+U+1)^e*(work+U+1)^2 := by gcongr <;> omega
    _ = _ := by rw [pow_add]; ring

private theorem high_loop_le (stream L n H U : ℕ)
    (hL : L ≤ U) (hn : n ≤ U) (hH : H ≤ U) :
    2^H*(stream+11*L+16*(n+2)+28*H+27)+3 ≤
      100*2^H*(stream+U+1) := by
  have hp : 1 ≤ 2^H := Nat.one_le_pow _ _ (by decide)
  have hb : stream+11*L+16*(n+2)+28*H+27+3 ≤ 100*(stream+U+1) := by omega
  have hm := Nat.mul_le_mul_left (2^H) hb
  nlinarith only [hm,hp]

/-- This is the actual high-loop expression, including copy/control/terminal
work. The high-variable factor stays separate from the retained-space cap. -/
theorem high_loop_budget_polynomial : ∃ C e : ℕ,
    ∀ n t d Q J A S work U L H : ℕ,
    n ≤ U → t ≤ U → d ≤ U → Q ≤ U → J ≤ U → A ≤ U → S ≤ U →
    L ≤ U → H ≤ U →
    2^H*(budget n t d Q J A S work+11*L+16*(n+2)+28*H+27)+3 ≤
      C*(U+1)^e*(work+1)^2*2^H := by
  obtain ⟨C,e,h⟩ := budget_polynomial
  refine ⟨100*(C+1),e+1,?_⟩
  intro n t d Q J A S work U L H hn ht hd hQ hJ hA hS hL hH
  have hb := h n t d Q J A S work U hn ht hd hQ hJ hA hS
  have hbase : 1 ≤ U+1 := by omega
  have hp : (U+1)^e ≤ (U+1)^(e+1) := Nat.pow_le_pow_right hbase (by omega)
  have hlin : U+1 ≤ (U+1)^(e+1)*(work+1)^2 :=
    (Nat.le_self_pow (by omega) _).trans
      (Nat.le_mul_of_pos_right _ (Nat.one_le_pow' _ _))
  have hb' := hb.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left C hp))
  have hsum : budget n t d Q J A S work+U+1 ≤
      (C+1)*(U+1)^(e+1)*(work+1)^2 := by nlinarith only [hb',hlin]
  calc
    _ ≤ 100*2^H*(budget n t d Q J A S work+U+1) := high_loop_le _ L n H U hL hn hH
    _ ≤ 100*2^H*((C+1)*(U+1)^(e+1)*(work+1)^2) := Nat.mul_le_mul_left _ hsum
    _ = _ := by ring


open SqrtLog SqrtLog.Statement
 theorem work_polynomial_runtime (coefficient e K p inputLength n U work H : ℕ)
    (A : ℝ) (hA : 0 ≤ A)
    (hU : U ≤ K*(inputLength+1)^p)
    (hwork : (work : ℝ) ≤ 17*(2 : ℝ)^(A*runtimeScale n))
    (hH : (H : ℝ) ≤ 64*runtimeScale n) :
    ((coefficient*(U+1)^e*(work+1)^2*2^H : ℕ) : ℝ) ≤
      runtimeBound ((coefficient : ℝ)*((K : ℝ)+1)^e*324)
        (2*A+64) (p*e) inputLength n := by
  have hinput : 1 ≤ (inputLength+1)^p := Nat.one_le_pow' _ _
  have huNat : U+1 ≤ (K+1)*(inputLength+1)^p := by nlinarith only [hU,hinput]
  have hu : (U : ℝ)+1 ≤ ((K : ℝ)+1)*((inputLength : ℝ)+1)^p := by exact_mod_cast huNat
  have hE : (1 : ℝ) ≤ (2 : ℝ)^(A*runtimeScale n) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hA (runtimeScale_nonneg n))
  have hw : (work : ℝ)+1 ≤ 18*(2 : ℝ)^(A*runtimeScale n) := by linarith
  have hh : ((2^H : ℕ) : ℝ) ≤ (2 : ℝ)^(64*runtimeScale n) := by
    push_cast
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hH
  have hm := mul_le_mul (mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hu e)
      (show (0 : ℝ) ≤ coefficient by positivity))
    (pow_le_pow_left₀ (by positivity) hw 2) (by positivity) (by positivity))
    hh (by positivity) (by positivity)
  push_cast at hm ⊢
  apply hm.trans_eq
  unfold runtimeBound
  rw [mul_pow, ← pow_mul, mul_pow,
    ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num only [Nat.cast_ofNat]
  rw [show A*runtimeScale n*(2 : ℝ) = (2*A)*runtimeScale n by ring]
  rw [show (coefficient : ℝ)*(((K : ℝ)+1)^e*((inputLength : ℝ)+1)^(p*e))*
      (324*(2 : ℝ)^((2*A)*runtimeScale n))*(2 : ℝ)^(64*runtimeScale n) =
      ((coefficient : ℝ)*((K : ℝ)+1)^e*324)*((inputLength : ℝ)+1)^(p*e)*
        ((2 : ℝ)^((2*A)*runtimeScale n)*(2 : ℝ)^(64*runtimeScale n)) by ring]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
  congr 2
  ring

/-- Uniform over all genuine resource records satisfying the sharp fields.
The caller derives those fields from the actual produced packing. -/
theorem high_loop_runtimeBound (k qi ql recordDegree K p : ℕ) :
    ∃ C A : ℝ, ∃ degree cutoff : ℕ, 1 ≤ C ∧ 1 ≤ A ∧ 1 ≤ degree ∧
      ∀ ambient ≥ cutoff, ∀ r : CostAssembly.Resources,
      CostAssembly.Bounds qi ql recordDegree ambient r →
      ∀ n t d Q J bankA S U L H inputLength : ℕ,
      n ≤ U → t ≤ U → d ≤ U → Q ≤ U → J ≤ U → bankA ≤ U → S ≤ U →
      L ≤ U → H ≤ U → H = r.branchVars → U ≤ K*(inputLength+1)^p →
      ((2^H*(QueryStreamCorrect.budget n t d Q J bankA S
          (CostAssembly.assembledWork k ambient r)+11*L+16*(n+2)+28*H+27)+3 : ℕ) : ℝ) ≤
        runtimeBound C A degree inputLength ambient := by
  obtain ⟨C,e,hpoly⟩ := high_loop_budget_polynomial
  obtain ⟨N,hN⟩ := CostAssembly.assembledWork_uniform_cutoff k qi ql recordDegree
  let coefficient : ℝ := (C : ℝ)*((K : ℝ)+1)^e*324
  let exponent := CostAssembly.exponentConstant k ql
  have hcoefficient : 0 ≤ coefficient := by dsimp [coefficient]; positivity
  have hexponent : 0 ≤ exponent := by dsimp [exponent,CostAssembly.exponentConstant]; positivity
  refine ⟨coefficient+1,2*exponent+64,p*e+1,N,by linarith,by linarith,by omega,?_⟩
  intro ambient hambient r hr n t d Q J bankA S U L H inputLength hn ht hd hQ hJ hA hS hL hH hHeq hU
  have hb := hpoly n t d Q J bankA S (CostAssembly.assembledWork k ambient r) U L H
    hn ht hd hQ hJ hA hS hL hH
  have hbranch : (H : ℝ) ≤ 64*runtimeScale ambient := by
    rw [hHeq]
    exact hr.branch.trans (CostAssembly.high_branch_exponent_le ambient)
  have h := work_polynomial_runtime C e K p inputLength ambient U
    (CostAssembly.assembledWork k ambient r) H exponent hexponent hU
    (hN ambient hambient r hr) hbranch
  have htime := (Nat.cast_le.mpr hb).trans h
  apply htime.trans
  apply (Execution.runtimeBound_mono_degree hcoefficient
    (show p*e ≤ p*e+1 by omega) inputLength ambient).trans
  unfold runtimeBound
  gcongr
  linarith



open Filter SqrtLog SqrtLog.Statement
/-- A rounded uniform query envelope and the actual chosen hash family stay
within one fixed power of the unchanged runtime scale. -/
theorem chosen_hash_query_polynomial_runtime (k coefficient power : ℕ)
    (C A : ℝ) (d : ℕ) (hC : 1 ≤ C) (hA : 1 ≤ A) (hd : 1 ≤ d) :
    ∃ cutoff : ℕ, ∀ n ≥ cutoff, ∀ m inputLength oldQuery measuredTime : ℕ,
      let B := 4*DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n)
        (by omega)^(k-1)
      m ≤ n*B → oldQuery ≤ Nat.ceil (runtimeBound C A d inputLength n) →
      measuredTime ≤ coefficient*(CostAssembly.hashCalls n m
        (SparseCode.distanceDenom m B)+oldQuery+inputLength+1)^power →
      (measuredTime : ℝ) ≤ runtimeBound ((coefficient : ℝ)*(4*C)^power)
        ((power : ℝ)*A) (d*power) inputLength n := by
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp
    ((CostAssembly.eventually_hashCalls_bound (2*(k-1)+1)).and
      (chosen_sparseBound_eventually_le_log2_power k))
  refine ⟨N,?_⟩
  intro n hn m inputLength oldQuery measuredTime B hm hquery htime
  obtain ⟨hcalls,hB⟩ := hN n hn
  have hB' : B ≤ Asymptotic.L n^(2*(k-1)+1) := by
    simpa only [B,Asymptotic.L] using hB
  have hh := hcalls m B hm hB'
  have hC0 : 0 ≤ C := by linarith
  have hA0 : 0 ≤ A := by linarith
  have he : (2 : ℝ)^runtimeScale n ≤ (2 : ℝ)^(A*runtimeScale n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by nlinarith [runtimeScale_nonneg n])
  have hpoly : 1 ≤ C*((inputLength : ℝ)+1)^d :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) inputLength; linarith))
  have hh' : (CostAssembly.hashCalls n m (SparseCode.distanceDenom m B) : ℝ) ≤
      runtimeBound C A d inputLength n := hh.trans
    (he.trans (le_mul_of_one_le_left (by positivity) hpoly))
  have hquery' : (oldQuery : ℝ) ≤ 2*runtimeBound C A d inputLength n :=
    (Nat.cast_le.mpr hquery).trans (Execution.ceil_runtimeBound_le hC hA0 d inputLength n)
  have hinput := Execution.input_le_runtimeBound hC hA0 (show 0<d by omega) inputLength n
  have hsum : ((CostAssembly.hashCalls n m (SparseCode.distanceDenom m B)+
      oldQuery+inputLength+1 : ℕ) : ℝ) ≤ 4*runtimeBound C A d inputLength n := by
    push_cast
    linarith
  have hcast : (measuredTime : ℝ) ≤ (coefficient : ℝ)*
      (((CostAssembly.hashCalls n m (SparseCode.distanceDenom m B)+oldQuery+inputLength+1 : ℕ) : ℝ))^power := by
    exact_mod_cast htime
  calc
    _ ≤ (coefficient : ℝ)*(4*runtimeBound C A d inputLength n)^power :=
      hcast.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hsum power) (by positivity))
    _ = _ := by
      rw [← runtimeBound_mul_constant, runtimeBound_pow, runtimeBound_mul_constant]


open SqrtLog SqrtLog.Statement
/-- Adding finitely many source phases preserves the same scale. -/
theorem runtimeBound_add_bound (C D A B : ℝ) (d e inputLength n : ℕ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    runtimeBound C A d inputLength n + runtimeBound D B e inputLength n ≤
      runtimeBound (C+D) (A+B) (d+e) inputLength n := by
  have hc := (runtimeBound_mono_exponent hC (show A ≤ A+B by linarith)
    d inputLength n).trans (Execution.runtimeBound_mono_degree hC
      (show d ≤ d+e by omega) inputLength n)
  have hd := (runtimeBound_mono_exponent hD (show B ≤ A+B by linarith)
    e inputLength n).trans (Execution.runtimeBound_mono_degree hD
      (show e ≤ d+e by omega) inputLength n)
  apply (add_le_add hc hd).trans_eq
  unfold runtimeBound
  ring

/-- Polynomial preprocessing and postprocessing are paid separately from the
stream/high core, with no exponential cost used as a storage cap. -/
theorem polynomial_overhead_runtime (C A : ℝ) (d K e inputLength n core extra : ℕ)
    (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hcore : (core : ℝ) ≤ runtimeBound C A d inputLength n)
    (hextra : extra ≤ K*(inputLength+1)^e) :
    ((core+extra : ℕ) : ℝ) ≤ runtimeBound (C+K) A (d+e) inputLength n := by
  have he : (extra : ℝ) ≤ runtimeBound K 0 e inputLength n := by
    simpa only [runtimeBound,zero_mul,Real.rpow_zero,mul_one,Nat.cast_mul,Nat.cast_pow,
      Nat.cast_add,Nat.cast_one] using (Nat.cast_le.mpr hextra : (extra : ℝ) ≤ (K*(inputLength+1)^e : ℕ))
  have h := (add_le_add hcore he).trans
    (runtimeBound_add_bound C K A 0 d e inputLength n hC (by positivity) hA (by norm_num))
  simpa only [Nat.cast_add,add_zero] using h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets

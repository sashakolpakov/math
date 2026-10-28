import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyUniform
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionFinalCostAlgebra

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Execution.SelectorCost
open Statement Filter CostAssembly Asymptotic
open scoped Topology

/-- The padding lives in W. All numeric search parameters use the original
ambient n. The candidate multiplicity is explicit, including failed trials. -/
def commonHeight (W n m B : ℕ) : ℕ :=
  (W+1)*(hashCalls n m (SparseCode.distanceDenom m B)+1)*(n+1)^4

 theorem commonHeight_bounds (W n m B : ℕ) (hn : 2 ≤ n) (hm : 0 < m)
    (hmn : m ≤ n^2) (hsize : Nat.size m ≤ n)
    (hP : SparseCode.distanceDenom m B ≤ n) :
    W ≤ commonHeight W n m B ∧ m ≤ commonHeight W n m B ∧
    3*m ≤ commonHeight W n m B ∧
    SparseCode.distanceDenom m B ≤ commonHeight W n m B ∧
    HashSelect.loopCap n m ≤ commonHeight W n m B ∧
    LeafParametersProgram.precision n m ≤ commonHeight W n m B ∧
    SparseCode.distanceDenom m B*W ≤ commonHeight W n m B ∧
    (3*m)^SparseCode.distanceDenom m B ≤ commonHeight W n m B := by
  let N := (3*m)^SparseCode.distanceDenom m B
  let F := hashCalls n m (SparseCode.distanceDenom m B)+1
  have hF : 1 ≤ F := by dsimp [F]; omega
  have hNF : N ≤ F := by
    have hK : 1 ≤ HashSelect.loopCap n m := by unfold HashSelect.loopCap; omega
    have hmul : N ≤ 2*N*HashSelect.loopCap n m*m := by
      calc
        N = 1*N*1*1 := by ring
        _ ≤ 2*N*HashSelect.loopCap n m*m := by gcongr <;> omega
    dsimp [F]
    change N ≤ 2*N*HashSelect.loopCap n m*m+1+1
    omega
  have hbase : (W+1)*(n+1)^4 ≤ commonHeight W n m B := by
    unfold commonHeight
    change (W+1)*(n+1)^4 ≤ (W+1)*F*(n+1)^4
    calc
      _ = (W+1)*1*(n+1)^4 := by ring
      _ ≤ _ := by gcongr
  have hp4 : 3*n^2+8*n+1 ≤ (n+1)^4 := by nlinarith [sq_nonneg (n*n)]
  have hpow : 1 ≤ (n+1)^4 := Nat.one_le_pow _ _ (by omega)
  have hplain : (n+1)^4 ≤ commonHeight W n m B := by
    apply le_trans _ hbase
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hsmall := hp4.trans hplain
  have hPW : SparseCode.distanceDenom m B*W ≤ commonHeight W n m B := by
    have hn4 : n ≤ (n+1)^4 := by nlinarith only [hp4]
    apply le_trans _ hbase
    calc
      _ ≤ (n+1)^4*(W+1) := Nat.mul_le_mul (hP.trans hn4) (by omega)
      _ = _ := by ring
  have hN : N ≤ commonHeight W n m B := by
    have hpow : 1 ≤ (n+1)^4 := Nat.one_le_pow _ _ (by omega)
    unfold commonHeight
    change N ≤ (W+1)*F*(n+1)^4
    calc
      _ ≤ F := hNF
      _ = 1*F*1 := by ring
      _ ≤ _ := by gcongr ; omega
  have hK : HashSelect.loopCap n m ≤ 8*n+1 := by unfold HashSelect.loopCap; omega
  have hp : LeafParametersProgram.precision n m ≤ 8*n+1 := by
    unfold LeafParametersProgram.precision; omega
  refine ⟨?_,by omega,by omega,by omega,by omega,by omega,hPW,hN⟩
  apply le_trans _ hbase
  calc
    W ≤ W+1 := by omega
    _ = (W+1)*1 := by ring
    _ ≤ _ := by gcongr

/-- Uniform in every sparse formula, and in arbitrarily padded W. -/
theorem eventually_commonHeight (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m B W : ℕ, m ≤ n*B → B ≤ L n^q →
      (commonHeight W n m B:ℝ)+1 ≤ runtimeBound 4 2 1 W n := by
  filter_upwards [eventually_hashCalls_bound q,eventually_polynomial_target 4]
    with n hc hp m B W hm hB
  have hh := hc m B hm hB
  let E := (2:ℝ)^runtimeScale n
  have hE : 1 ≤ E := Real.one_le_rpow (by norm_num) (runtimeScale_nonneg n)
  have hW : (1:ℝ) ≤ (W:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) W; linarith
  have hhc : (hashCalls n m (SparseCode.distanceDenom m B):ℝ)+1 ≤ 2*E := by
    change (hashCalls n m (SparseCode.distanceDenom m B):ℝ) ≤ E at hh
    linarith
  have hp' : (((n+1)^4:ℕ):ℝ) ≤ E := hp
  have hheight : (commonHeight W n m B:ℝ) ≤ 2*((W:ℝ)+1)*(E*E) := by
    unfold commonHeight
    push_cast
    calc
      _ ≤ ((W:ℝ)+1)*(2*E)*E := by gcongr; exact_mod_cast hp'
      _ = _ := by ring
  have he2 : E*E = (2:ℝ)^(2*runtimeScale n) := by
    dsimp [E]
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  unfold runtimeBound
  simp only [pow_one]
  rw [← he2]
  nlinarith [mul_le_mul hE hE (by norm_num : (0:ℝ) ≤ 1) (by linarith)]

 theorem eventually_commonHeight_bounds (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m B W : ℕ, 0 < m → m ≤ n*B → B ≤ L n^q →
      W ≤ commonHeight W n m B ∧ m ≤ commonHeight W n m B ∧
      3*m ≤ commonHeight W n m B ∧ SparseCode.distanceDenom m B ≤ commonHeight W n m B ∧
      HashSelect.loopCap n m ≤ commonHeight W n m B ∧
      LeafParametersProgram.precision n m ≤ commonHeight W n m B ∧
      SparseCode.distanceDenom m B*W ≤ commonHeight W n m B ∧
      (3*m)^SparseCode.distanceDenom m B ≤ commonHeight W n m B := by
  filter_upwards [eventually_sparse_parameter_bounds q,
    eventually_L_power_le_n (2*q+3) (by norm_num : (0:ℝ) < 1),eventually_ge_atTop 2]
    with n hpar hpow hn m B W hm hmn hB
  obtain ⟨hs,hm2,hP⟩ := hpar m B hmn hB
  have hp : L n^(2*q+3) ≤ n := by exact_mod_cast (by simpa using hpow : (L n:ℝ)^(2*q+3) ≤ n)
  exact commonHeight_bounds W n m B hn hm hm2 hs (hP.trans hp)

end SubexponentialSAT.SqrtLog.Execution.SelectorCost

end OAI.Algorithms

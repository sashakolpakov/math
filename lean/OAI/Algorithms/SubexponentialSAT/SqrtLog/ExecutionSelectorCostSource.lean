import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupOuterCostMajorant
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionSelectorCostParameters

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Execution.SelectorCost
open Statement Filter CostAssembly Asymptotic
open scoped Topology

/-- Physical marked/accepted query size after the selected-row history. -/
def physicalSource (V width P K m : ℕ) : ℕ :=
  7*(V+K*(2*P*width+2)+P*width)+m+2

 theorem physicalSource_mono {V V' width width' P K m : ℕ}
    (hV : V ≤ V') (hw : width ≤ width') :
    physicalSource V width P K m ≤ physicalSource V' width' P K m := by
  unfold physicalSource
  gcongr

 theorem physicalSource_le (V width P K m n : ℕ)
    (hw : width ≤ V) (hP : P ≤ n) (hK : K ≤ 8*n) (hm : m ≤ n^2) :
    physicalSource V width P K m+1 ≤ 200*(n+1)^2*(V+1) := by
  have h : physicalSource V width P K m+1 ≤
      7*(V+8*n*(2*n*V+2)+n*V)+n^2+3 := by
    unfold physicalSource
    change 7*(V+K*(2*P*width+2)+P*width)+m+2+1 ≤
      7*(V+8*n*(2*n*V+2)+n*V)+n^2+2+1
    gcongr
  apply h.trans
  ring_nf
  omega

 def initialSize (C d q p n W : ℕ) : ℕ :=
  W+CodeSetupOuterCost.setupMajorant C d q n*(W+1)^p

 theorem initialSize_le (C d q p n W : ℕ) :
    initialSize C d q p n W+1 ≤
      2*CodeSetupOuterCost.setupMajorant C d q n*(W+1)^(p+1) := by
  have hM : 1 ≤ CodeSetupOuterCost.setupMajorant C d q n :=
    Nat.one_le_pow _ _ (by omega)
  have hpow : (W+1)^p ≤ (W+1)^(p+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hW : W+1 ≤ (W+1)^(p+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < W+1) (by omega : 1 ≤ p+1)
  have hWM : W+1 ≤ CodeSetupOuterCost.setupMajorant C d q n*(W+1)^(p+1) :=
    hW.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hpM := Nat.mul_le_mul_left (CodeSetupOuterCost.setupMajorant C d q n) hpow
  unfold initialSize
  nlinarith only [hWM,hpM]

/-- Uniform in every formula and padded original input. This includes the
entire actual initial code construction through its certified majorant. -/
theorem eventually_physicalSource (C d q p : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m B W V width : ℕ,
      m ≤ n*B → B ≤ L n^q → V ≤ initialSize C d q p n W → width ≤ V →
      (physicalSource V width (SparseCode.distanceDenom m B) (HashSelect.loopCap n m) m:ℝ)+1 ≤
        runtimeBound 400 2 (p+1) W n := by
  filter_upwards [CodeSetupOuterCost.setupMajorant_target C d q,
    eventually_polynomial_target 2,eventually_sparse_parameter_bounds q,
    eventually_L_power_le_n (2*q+3) (by norm_num : (0:ℝ) < 1),eventually_ge_atTop 2]
    with n hsetup hpoly hpar hPn hn m B W V width hm hB hV hw
  obtain ⟨hsize,hm2,hP⟩ := hpar m B hm hB
  have hP' : SparseCode.distanceDenom m B ≤ n := by
    apply hP.trans
    exact_mod_cast (by simpa using hPn : (L n:ℝ)^(2*q+3) ≤ n)
  have hK : HashSelect.loopCap n m ≤ 8*n := by unfold HashSelect.loopCap; omega
  have hs := physicalSource_le V width (SparseCode.distanceDenom m B)
    (HashSelect.loopCap n m) m n hw hP' hK hm2
  have hi := initialSize_le C d q p n W
  have hVi : V+1 ≤ 2*CodeSetupOuterCost.setupMajorant C d q n*(W+1)^(p+1) := by omega
  have hsr : (physicalSource V width (SparseCode.distanceDenom m B)
      (HashSelect.loopCap n m) m:ℝ)+1 ≤ 200*((n:ℝ)+1)^2*((V:ℝ)+1) := by exact_mod_cast hs
  have hVir : (V:ℝ)+1 ≤ 2*(CodeSetupOuterCost.setupMajorant C d q n:ℝ)*((W:ℝ)+1)^(p+1) := by
    exact_mod_cast hVi
  have hpolyr : ((n:ℝ)+1)^2 ≤ (2:ℝ)^runtimeScale n := by exact_mod_cast hpoly
  calc
    _ ≤ 200*((2:ℝ)^runtimeScale n)*
        (2*((2:ℝ)^runtimeScale n)*((W:ℝ)+1)^(p+1)) := by
      apply hsr.trans
      gcongr
      exact hVir.trans (by gcongr)
    _ = runtimeBound 400 2 (p+1) W n := by
      unfold runtimeBound
      rw [show (2:ℝ)*runtimeScale n=runtimeScale n+runtimeScale n by ring,
        Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      ring

end SubexponentialSAT.SqrtLog.Execution.SelectorCost

end OAI.Algorithms

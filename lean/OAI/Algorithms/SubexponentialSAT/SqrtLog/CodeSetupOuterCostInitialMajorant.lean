import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupOuterCostMajorant

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSetupOuterCost
open SubexponentialSAT Filter CostAssembly Asymptotic
open scoped Topology

/-- The actual startup and four construction stages are bounded by an explicit
padding-independent resource and a fixed polynomial in physical input length.
The resource itself satisfies `setupMajorant_target` with coefficient one. -/
theorem initial_resource_bound :
    ∃ C d p : ℕ, ∀ q : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ m B W (records : List (List Bool)) (mword Bword qword Dword countWord : List Bool)
        (s : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B),
      0 < m → 0 < B → m ≤ n*B → B ≤ L n^q →
      (Encoding.encodeList id records).length ≤ W →
      mword.length ≤ W+LeafOuterProgram.startBudget W records →
      Bword.length ≤ W+LeafOuterProgram.startBudget W records →
      countWord.length ≤ W+LeafOuterProgram.startBudget W records →
      qword.length ≤ mword.length+Bword.length+11 →
      Dword.length ≤ 4*mword.length+2*Bword.length+30 →
      LeafOuterProgram.startBudget W records+
        LeafOuterProgram.constructBudget (W+LeafOuterProgram.startBudget W records)
          mword Bword qword Dword countWord s Q ≤ setupMajorant C d q n*(W+1)^p := by
  obtain ⟨C,d,p,hbound⟩ := construct_power_bound
  let C' := startupConstant+C*(startupConstant+2)^p
  refine ⟨C',d,4*p+4,?_⟩
  intro q
  filter_upwards [eventually_L_power_le_n q (by norm_num : (0:ℝ) < 1),eventually_ge_atTop 16]
    with n hLn hn m B W records mword Bword qword Dword countWord s Q
      hm hB hmn hBn hrecords hmw hBw hcw hqw hDw
  have hln : L n^q ≤ n := by exact_mod_cast (by simpa using hLn : (L n:ℝ)^q ≤ n)
  have hm2 : m ≤ n^2 := by nlinarith [hBn.trans hln]
  let T := LeafOuterProgram.startBudget W records
  let Y := (W+1)^(4*p+4)
  let P := (n+1)^(d+searchExponent q n)
  have hP : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have hT : T ≤ startupConstant*(W+1)^4 := startBudget_bound W records hrecords
  have hW : W+T+1 ≤ (startupConstant+2)*(W+1)^4 := by
    have hw : W+1 ≤ (W+1)^4 := by simpa using Nat.pow_le_pow_right (by omega : 1 ≤ W+1) (by decide : 1 ≤ 4)
    nlinarith only [hT,hw]
  have hY4 : (W+1)^4 ≤ Y := Nat.pow_le_pow_right (by omega) (by omega)
  have hYp : (W+1)^(4*p) ≤ Y := Nat.pow_le_pow_right (by omega) (by omega)
  have hstart : T ≤ startupConstant*P*Y := by
    calc
      _ ≤ startupConstant*(W+1)^4 := hT
      _ ≤ startupConstant*Y := Nat.mul_le_mul_left _ hY4
      _ ≤ startupConstant*P*Y := by simpa only [Nat.mul_one] using Nat.mul_le_mul_right Y (Nat.mul_le_mul_left startupConstant hP)
  have hc := hbound q n m B (W+T) mword Bword qword Dword countWord s Q
    hn hm hB hm2 hmn hBn hmw hBw hcw hqw hDw
  have hp : (W+T+1)^p ≤ (startupConstant+2)^p*Y := by
    calc
      _ ≤ ((startupConstant+2)*(W+1)^4)^p := Nat.pow_le_pow_left hW _
      _ = (startupConstant+2)^p*(W+1)^(4*p) := by rw [mul_pow,←pow_mul]
      _ ≤ _ := Nat.mul_le_mul_left _ hYp
  have hc' : LeafOuterProgram.constructBudget (W+T) mword Bword qword Dword countWord s Q ≤
      C*(startupConstant+2)^p*P*Y := by
    calc
      _ ≤ C*P*(W+T+1)^p := hc
      _ ≤ C*P*((startupConstant+2)^p*Y) := Nat.mul_le_mul_left _ hp
      _ = _ := by ring
  calc
    _ ≤ startupConstant*P*Y+C*(startupConstant+2)^p*P*Y := Nat.add_le_add hstart hc'
    _ = C'*P*Y := by dsimp [C']; ring
    _ ≤ setupMajorant C' d q n*Y := Nat.mul_le_mul_right _ (coefficient_absorb C' d q n (by omega))

end SubexponentialSAT.SqrtLog.CodeSetupOuterCost

end OAI.Algorithms

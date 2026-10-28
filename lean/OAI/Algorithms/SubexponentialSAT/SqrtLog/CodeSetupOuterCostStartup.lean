import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupOuterCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupOuterCostStartupBounds

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSetupOuterCost
open SubexponentialSAT Filter CostAssembly Asymptotic
open scoped Topology

/-- Startup plus the literal constructor expression used by initialCode_eval.
All generated-word padding is retained through the post-start WordBound. -/
theorem eventually_initialBudget (q : ℕ) :
    ∃ C d : ℕ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ m B W (records : List (List Bool)) (mword Bword qword Dword countWord : List Bool)
        (s : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B),
      0 < m → 0 < B → m ≤ n*B → B ≤ L n^q →
      (Encoding.encodeList id records).length ≤ W →
      mword.length ≤ W+LeafOuterProgram.startBudget W records →
      Bword.length ≤ W+LeafOuterProgram.startBudget W records →
      countWord.length ≤ W+LeafOuterProgram.startBudget W records →
      qword.length ≤ mword.length+Bword.length+11 →
      Dword.length ≤ 4*mword.length+2*Bword.length+30 →
      ((LeafOuterProgram.startBudget W records+
        LeafOuterProgram.constructBudget (W+LeafOuterProgram.startBudget W records)
          mword Bword qword Dword countWord s Q:ℕ):ℝ) ≤
        (C:ℝ)*((W:ℝ)+1)^d*(2:ℝ)^Statement.runtimeScale n := by
  obtain ⟨C,d,hC,hbound⟩ := eventually_constructBudget q
  refine ⟨startupConstant+C*(startupConstant+2)^d,4*d+4,by positivity,?_⟩
  filter_upwards [hbound] with n hn m B W records mword Bword qword Dword countWord s Q
    hm hB hmn hBn hrecords hmw hBw hcw hqw hDw
  let T := LeafOuterProgram.startBudget W records
  let E : ℝ := (2:ℝ)^Statement.runtimeScale n
  have hE : 1 ≤ E := Real.one_le_rpow (by norm_num) (Statement.runtimeScale_nonneg n)
  have hW : (1:ℝ) ≤ (W:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) W; linarith
  have htN : T ≤ startupConstant*(W+1)^4 := startBudget_bound W records hrecords
  have htR : (T:ℝ) ≤ (startupConstant:ℝ)*((W:ℝ)+1)^4 := by exact_mod_cast htN
  have hwR : ((W+T:ℕ):ℝ)+1 ≤ ((startupConstant:ℝ)+2)*((W:ℝ)+1)^4 := by
    have hp : (W:ℝ)+1 ≤ ((W:ℝ)+1)^4 := by simpa using pow_le_pow_right₀ hW (by decide : 1 ≤ 4)
    push_cast
    nlinarith only [htR,hp]
  have hmain := hn m B (W+T) mword Bword qword Dword countWord s Q
    hm hB hmn hBn hmw hBw hcw hqw hDw
  have hpow : (((W+T:ℕ):ℝ)+1)^d ≤ ((startupConstant:ℝ)+2)^d*((W:ℝ)+1)^(4*d) := by
    calc
      _  ≤  (((startupConstant:ℝ)+2)*((W:ℝ)+1)^4)^d := pow_le_pow_left₀ (by have := Nat.cast_nonneg (α:=ℝ) (W+T); linarith) hwR d
      _ = _ := by rw [mul_pow,←pow_mul]
  have hsmall : ((W:ℝ)+1)^4 ≤ ((W:ℝ)+1)^(4*d+4) := pow_le_pow_right₀ hW (by omega)
  have hlarge : ((W:ℝ)+1)^(4*d) ≤ ((W:ℝ)+1)^(4*d+4) := pow_le_pow_right₀ hW (by omega)
  have hstart : (T:ℝ) ≤ (startupConstant:ℝ)*((W:ℝ)+1)^(4*d+4)*E := by
    calc
      _  ≤  (startupConstant:ℝ)*((W:ℝ)+1)^4 := htR
      _  ≤  (startupConstant:ℝ)*((W:ℝ)+1)^(4*d+4)*E := by
        calc
          _  ≤  (startupConstant:ℝ)*((W:ℝ)+1)^(4*d+4)*1 := by simpa using mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg startupConstant)
          _  ≤  _ := mul_le_mul_of_nonneg_left hE (mul_nonneg (Nat.cast_nonneg startupConstant) (by positivity))
  have hconstruct : (LeafOuterProgram.constructBudget (W+T) mword Bword qword Dword countWord s Q:ℝ) ≤
      (C:ℝ)*((startupConstant:ℝ)+2)^d*((W:ℝ)+1)^(4*d+4)*E := by
    calc
      _  ≤  (C:ℝ)*(((W+T:ℕ):ℝ)+1)^d*E := hmain
      _  ≤  (C:ℝ)*(((startupConstant:ℝ)+2)^d*((W:ℝ)+1)^(4*d))*E := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg C)) (by linarith)
      _ = (C:ℝ)*((startupConstant:ℝ)+2)^d*((W:ℝ)+1)^(4*d)*E := by ring
      _  ≤  _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlarge (mul_nonneg (Nat.cast_nonneg C) (pow_nonneg (add_nonneg (Nat.cast_nonneg startupConstant) (by norm_num)) _))) (by linarith)
  change ((T+_:ℕ):ℝ) ≤ _
  push_cast
  calc
    _  ≤  (startupConstant:ℝ)*((W:ℝ)+1)^(4*d+4)*E+
        (C:ℝ)*((startupConstant:ℝ)+2)^d*((W:ℝ)+1)^(4*d+4)*E := add_le_add hstart hconstruct
    _ = _ := by dsimp [E]; ring

end SubexponentialSAT.SqrtLog.CodeSetupOuterCost

end OAI.Algorithms

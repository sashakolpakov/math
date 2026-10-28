import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupOuterCostOrdinary
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramConstruct

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSetupOuterCost
open SubexponentialSAT Filter CostAssembly Asymptotic
open scoped Topology

/-- Ordinary polynomial dependence on the sparse leaf size is absorbed
uniformly, while physical input padding remains separate. -/
theorem eventually_clause_polynomial (q d : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m B : ℕ, m ≤ n*B → B ≤ L n^q →
      ((m:ℝ)+16)^d ≤ (2:ℝ)^Statement.runtimeScale n := by
  have hd : ∀ᶠ n : ℕ in atTop,
      ((3*d:ℕ):ℝ) ≤ ((3*d+1:ℕ):ℝ)*(L n:ℝ)^0 := by
    filter_upwards [] with n
    simp only [pow_zero,mul_one]
    exact_mod_cast Nat.le_succ (3*d)
  have ht := eventually_polylog_degree_target (fun _ => 3*d) 0
    (show (0:ℝ) < ((3*d+1:ℕ):ℝ) by positivity) hd
  have hL := eventually_L_power_le_n q (by norm_num : (0:ℝ) < 1)
  filter_upwards [ht,hL,eventually_ge_atTop 16] with n hn hLn hlarge m B hm hB
  have hln : L n^q ≤ n := by exact_mod_cast (by simpa using hLn : (L n:ℝ)^q ≤ n)
  have hm2 : m ≤ n^2 := by nlinarith [hB.trans hln]
  have hm3 : m+16 ≤ (n+1)^3 := by nlinarith
  have hp : (m+16)^d ≤ (n+1)^(3*d) := by
    calc
      _  ≤  ((n+1)^3)^d := Nat.pow_le_pow_left hm3 d
      _ = _ := by rw [← pow_mul]
  have hpR : ((m:ℝ)+16)^d ≤ (((n+1)^(3*d):ℕ):ℝ) := by exact_mod_cast hp
  exact hpR.trans hn

theorem constructBudget_eq {m B : ℕ} (W : ℕ)
    (mword Bword qword Dword width : List Bool)
    (s : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B) :
    LeafOuterProgram.constructBudget W mword Bword qword Dword width s Q =
      staged W (CodeParametersProgram.fullBudget m B mword.length Bword.length)
        (CodeSearchProgram.localProgramBudget (SparseCode.localRows m B)
          (SparseCode.degree m B) (SparseCode.degree m B/(100*B*SparseCode.logSize m)+1))
        (CodeSearchProgram.graphProgramBudget (SparseCode.degree m B)
          (SparseCode.dimension m B) qword.length Dword.length)
        (CodeRowsProgram.cost Dword mword width s Q) := rfl

/-- Exact native construction budget, uniformly for every supplied matrix.
The decoder width is the actual immutable count word, with all padding paid
through W; it is never replaced by the bit length of its numerical value. -/
theorem eventually_constructBudget (q : ℕ) :
    ∃ C d : ℕ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ m B W (mword Bword qword Dword countWord : List Bool)
        (s : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B),
      0 < m → 0 < B → m ≤ n*B → B ≤ L n^q →
      mword.length ≤ W → Bword.length ≤ W → countWord.length ≤ W →
      qword.length ≤ mword.length+Bword.length+11 →
      Dword.length ≤ 4*mword.length+2*Bword.length+30 →
      (LeafOuterProgram.constructBudget W mword Bword qword Dword countWord s Q:ℝ) ≤
        (C:ℝ)*((W:ℝ)+1)^d*(2:ℝ)^Statement.runtimeScale n := by
  obtain ⟨A,e,hA⟩ := ordinary_bound
  refine ⟨10001^4*(A+31^6),e+6,by positivity,?_⟩
  filter_upwards [eventually_clause_polynomial q e,
    CodeSetupCost.eventually_constructedBudget_with_words 1 1 q]
    with n hn hs m B W mword Bword qword Dword countWord s Q hm hB hmn hBn hmw hBw hcw hqw hDw
  let p := CodeParametersProgram.fullBudget m B mword.length Bword.length
  let l := CodeSearchProgram.localProgramBudget (SparseCode.localRows m B)
    (SparseCode.degree m B) (SparseCode.degree m B/(100*B*SparseCode.logSize m)+1)
  let g := CodeSearchProgram.graphProgramBudget (SparseCode.degree m B)
    (SparseCode.dimension m B) qword.length Dword.length
  let z := CodeRowsProgram.cost Dword mword countWord s Q
  let E : ℝ := (2:ℝ)^Statement.runtimeScale n
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hW : (1:ℝ) ≤ (W:ℝ)+1 := by
    have := Nat.cast_nonneg (α:=ℝ) W
    linarith
  have he : ((W:ℝ)+1)^e ≤ ((W:ℝ)+1)^(e+6) :=
    pow_le_pow_right₀ hW (by omega)
  have h6 : ((W:ℝ)+1)^6 ≤ ((W:ℝ)+1)^(e+6) :=
    pow_le_pow_right₀ hW (by omega)
  have hpN := hA m B W mword Bword Dword countWord s Q hm hB hmw hBw (by omega) hcw
  have hpR : ((W+p+z+2:ℕ):ℝ) ≤ (A:ℝ)*(inputSize m W:ℝ)^e := by exact_mod_cast hpN
  have hprod : (inputSize m W:ℝ) ≤ ((m:ℝ)+16)*((W:ℝ)+1) := by
    exact_mod_cast sum_input_le_product m W
  have ho : ((W+p+z+2:ℕ):ℝ) ≤ (A:ℝ)*((W:ℝ)+1)^(e+6)*E := by
    calc
      _  ≤  (A:ℝ)*(inputSize m W:ℝ)^e := hpR
      _  ≤  (A:ℝ)*(((m:ℝ)+16)*((W:ℝ)+1))^e := by gcongr
      _ = (A:ℝ)*((m:ℝ)+16)^e*((W:ℝ)+1)^e := by rw [mul_pow]; ring
      _  ≤  (A:ℝ)*E*((W:ℝ)+1)^(e+6) := by gcongr; exact hn m B hmn hBn
      _ = _ := by ring
  have hh := hs m B qword.length Dword.length hm hB hmn hBn
  have hh' : ((l+g+1:ℕ):ℝ) ≤ ((max qword.length Dword.length:ℕ)+1:ℝ)^6*E := by
    simpa only [CodeSetupCost.constructedBudget,CodeSetupCost.nativeBudget,one_mul,l,g,E] using hh
  have hwN := word_bound W qword.length Dword.length (by omega) (by omega)
  have hwR : ((max qword.length Dword.length:ℕ)+1:ℝ) ≤ 31*((W:ℝ)+1) := by exact_mod_cast hwN
  have hhR : ((l+g+1:ℕ):ℝ) ≤ (31:ℝ)^6*((W:ℝ)+1)^(e+6)*E := by
    calc
      _  ≤  ((max qword.length Dword.length:ℕ)+1:ℝ)^6*E := hh'
      _  ≤  (31*((W:ℝ)+1))^6*E := by gcongr
      _ = (31:ℝ)^6*((W:ℝ)+1)^6*E := by rw [mul_pow]
      _  ≤  _ := by gcongr
  have hbN : LeafOuterProgram.constructBudget W mword Bword qword Dword countWord s Q ≤
      10001^4*((W+p+z+2)+(l+g+1)) := by
    rw [constructBudget_eq]
    exact (staged_le W p l g z).trans (Nat.mul_le_mul_left _ (by omega))
  calc
    _  ≤  (10001:ℝ)^4*(((W+p+z+2:ℕ):ℝ)+((l+g+1:ℕ):ℝ)) := by exact_mod_cast hbN
    _  ≤  (10001:ℝ)^4*((A:ℝ)*((W:ℝ)+1)^(e+6)*E+(31:ℝ)^6*((W:ℝ)+1)^(e+6)*E) := by gcongr
    _ = _ := by push_cast; ring

end SubexponentialSAT.SqrtLog.CodeSetupOuterCost

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupOuterCostStartup

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSetupOuterCost
open SubexponentialSAT Filter CostAssembly Asymptotic
open scoped Topology

/-- Padding-independent exponent for the two actual exhaustive searches. -/
def searchExponent (q n : ℕ) : ℕ :=
  CodeSetupCost.exponent (CodeSetupCost.fixedConstant 1 1)
    (CodeSetupCost.heightCoefficient q * L n^(2*q+3))

/-- An explicit integer resource count; physical padding is charged separately. -/
def setupMajorant (C d q n : ℕ) : ℕ := (n+1)^(C+d+searchExponent q n)

theorem setupMajorant_target (C d q : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (setupMajorant C d q n : ℝ) ≤ (2:ℝ)^Statement.runtimeScale n := by
  let K := C+d+CodeSetupCost.degreeConstant
    (CodeSetupCost.fixedConstant 1 1) (CodeSetupCost.heightCoefficient q) 0
  have hK : (0:ℝ) < K := by dsimp [K,CodeSetupCost.degreeConstant]; positivity
  have hd : ∀ᶠ n : ℕ in atTop,
      ((C+d+searchExponent q n:ℕ):ℝ) ≤ (K:ℝ)*(L n:ℝ)^(2*(2*q+3)) := by
    filter_upwards [] with n
    have he := CodeSetupCost.exponent_le (CodeSetupCost.fixedConstant 1 1)
      (CodeSetupCost.heightCoefficient q)
      (CodeSetupCost.heightCoefficient q * L n^(2*q+3)) 0 n (2*q+3) (by rfl)
    have hp : 1 ≤ L n^(2*(2*q+3)) := Nat.one_le_pow _ _ (L_pos n)
    have hb : C+d+searchExponent q n ≤ K*L n^(2*(2*q+3)) := by
      dsimp [K,searchExponent]
      nlinarith
    exact_mod_cast hb
  exact eventually_polylog_degree_target (fun n => C+d+searchExponent q n)
    (2*(2*q+3)) hK hd

theorem coefficient_absorb (C d q n : ℕ) (hn : 2 ≤ n) :
    C*(n+1)^(d+searchExponent q n) ≤ setupMajorant C d q n := by
  have hc : C ≤ (n+1)^C :=
    (CodeSetupCost.self_le_three_pow C).trans (Nat.pow_le_pow_left (by omega) C)
  calc
    _ ≤ (n+1)^C*(n+1)^(d+searchExponent q n) := Nat.mul_le_mul_right _ hc
    _ = _ := by unfold setupMajorant; rw [←pow_add]; congr 1; omega

/-- Concrete entire-constructor bound before absorbing the fixed coefficient.
Only the displayed polynomial factor depends on physical metadata padding. -/
theorem construct_power_bound :
    ∃ C d p : ℕ, ∀ q n m B W (mword Bword qword Dword countWord : List Bool)
      (s : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B),
      16 ≤ n → 0 < m → 0 < B → m ≤ n^2 → m ≤ n*B → B ≤ L n^q →
      mword.length ≤ W → Bword.length ≤ W → countWord.length ≤ W →
      qword.length ≤ mword.length+Bword.length+11 →
      Dword.length ≤ 4*mword.length+2*Bword.length+30 →
      LeafOuterProgram.constructBudget W mword Bword qword Dword countWord s Q ≤
        C*(n+1)^(d+searchExponent q n)*(W+1)^p := by
  obtain ⟨A,e,hA⟩ := ordinary_bound
  refine ⟨10001^4*(A+31^6),3*e,e+6,?_⟩
  intro q n m B W mword Bword qword Dword countWord s Q hn hm hB hm2 hmn hBn hmw hBw hcw hqw hDw
  let P := CodeParametersProgram.fullBudget m B mword.length Bword.length
  let T := CodeSearchProgram.localProgramBudget (SparseCode.localRows m B)
    (SparseCode.degree m B) (SparseCode.degree m B/(100*B*SparseCode.logSize m)+1)
  let G := CodeSearchProgram.graphProgramBudget (SparseCode.degree m B)
    (SparseCode.dimension m B) qword.length Dword.length
  let Z := CodeRowsProgram.cost Dword mword countWord s Q
  have ho := hA m B W mword Bword Dword countWord s Q hm hB hmw hBw (by omega) hcw
  have hi : inputSize m W ≤ (n+1)^3*(W+1) := by
    apply (sum_input_le_product m W).trans
    exact Nat.mul_le_mul_right _ (by nlinarith : m+16 ≤ (n+1)^3)
  have hpw : (W+1)^e ≤ (W+1)^(e+6) := Nat.pow_le_pow_right (by omega) (by omega)
  have hpn : (n+1)^(3*e) ≤ (n+1)^(3*e+searchExponent q n) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have ho' : W+P+Z+2 ≤ A*(n+1)^(3*e+searchExponent q n)*(W+1)^(e+6) := by
    calc
      _ ≤ A*(inputSize m W)^e := ho
      _ ≤ A*((n+1)^3*(W+1))^e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hi _)
      _ = A*(n+1)^(3*e)*(W+1)^e := by rw [mul_pow,←pow_mul]; ring
      _ ≤ _ := by gcongr
  have hs := CodeSetupCost.constructedBudget_le 1 1 m B qword.length Dword.length hm hB
  have hh := CodeSetupCost.height_le n m B q hmn hBn
  have hex : CodeSetupCost.exponent (CodeSetupCost.fixedConstant 1 1) (CodeSetupCost.height m B) ≤
      searchExponent q n := by
    dsimp [searchExponent,CodeSetupCost.exponent]
    nlinarith
  have hs' : T+G+1 ≤ (n+1)^(searchExponent q n)*(31*(W+1))^6 := by
    have hw := word_bound W qword.length Dword.length (by omega) (by omega)
    calc
      _ ≤ CodeSetupCost.envelope (CodeSetupCost.fixedConstant 1 1)
          (CodeSetupCost.height m B) (max qword.length Dword.length) := by
        simpa only [CodeSetupCost.constructedBudget,CodeSetupCost.nativeBudget,one_mul,T,G] using hs
      _ ≤ (n+1)^(searchExponent q n)*(31*(W+1))^6 := by
        unfold CodeSetupCost.envelope
        exact Nat.mul_le_mul
          ((Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) hex))
          (Nat.pow_le_pow_left hw _)
  have hgn : (n+1)^(searchExponent q n) ≤ (n+1)^(3*e+searchExponent q n) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hgw : (W+1)^6 ≤ (W+1)^(e+6) := Nat.pow_le_pow_right (by omega) (by omega)
  have hs'' : T+G+1 ≤ 31^6*(n+1)^(3*e+searchExponent q n)*(W+1)^(e+6) := by
    calc
      _ ≤ (n+1)^(searchExponent q n)*(31*(W+1))^6 := hs'
      _ = 31^6*(n+1)^(searchExponent q n)*(W+1)^6 := by rw [mul_pow]; ring
      _ ≤ _ := by gcongr
  have hb : LeafOuterProgram.constructBudget W mword Bword qword Dword countWord s Q ≤
      10001^4*((W+P+Z+2)+(T+G+1)) := by
    rw [constructBudget_eq]
    exact (staged_le W P T G Z).trans (Nat.mul_le_mul_left _ (by omega))
  calc
    _ ≤ 10001^4*((W+P+Z+2)+(T+G+1)) := hb
    _ ≤ 10001^4*(A*(n+1)^(3*e+searchExponent q n)*(W+1)^(e+6)+
        31^6*(n+1)^(3*e+searchExponent q n)*(W+1)^(e+6)) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add ho' hs'')
    _ = _ := by ring

end SubexponentialSAT.SqrtLog.CodeSetupOuterCost

end OAI.Algorithms

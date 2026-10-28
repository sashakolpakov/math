import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupOuterCostPolynomial
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgramBudget
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramCost

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSetupOuterCost
open SubexponentialSAT

def inputSize (m W : ℕ) : ℕ := m+W+16

theorem serializer_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (W : ℕ) (mword Dword width : List Bool)
    (s : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (hmw : mword.length ≤ W) (hDw : Dword.length ≤ 6*W+30) (hb : width.length ≤ W) :
    CodeRowsProgram.cost Dword mword width s Q  ≤
      (10000000*9^6)*(inputSize m W)^6 := by
  let X := inputSize m W
  have hX : 1 ≤ X := by dsimp [X,inputSize]; omega
  have hD := SparseCode.degree_le m B
  have hp := SparseCode.degree_pos hm hB
  have he := SparseCode.graph_edge_upper hm hB
  have hN : 2^SparseCode.dimension m B ≤ 2*m := by nlinarith
  have hr : SparseCode.dimension m B ≤ 2*m :=
    (Nat.lt_two_pow_self.le).trans hN
  have ht : SparseCode.localRows m B ≤ m+1 := by
    have hd := Nat.div_le_self (SparseCode.degree m B) (8*B)
    unfold SparseCode.localRows
    omega
  rw [CodeRowsProgram.cost_eq_explicit
    (r := SparseCode.dimension m B) (D := SparseCode.degree m B)
    (t := SparseCode.localRows m B) Dword mword width s Q]
  change serial (2^SparseCode.dimension m B) (SparseCode.dimension m B)
    (SparseCode.degree m B) (SparseCode.localRows m B) width.length Dword.length mword.length  ≤  _
  have hs := serial_le (2^SparseCode.dimension m B) (SparseCode.dimension m B)
    (SparseCode.degree m B) (SparseCode.localRows m B) width.length Dword.length mword.length (8*X)
    (by dsimp [X,inputSize]; omega) (by dsimp [X,inputSize]; omega)
    (by dsimp [X,inputSize]; omega) (by dsimp [X,inputSize]; omega)
    (by dsimp [X,inputSize]; omega) (by dsimp [X,inputSize]; omega)
    (by dsimp [X,inputSize]; omega)
  calc
    _  ≤  10000000*(8*X+1)^6 := hs
    _  ≤  10000000*(9*X)^6 := by gcongr; omega
    _ = _ := by dsimp [X]; ring

/-- Every non-search term is an ordinary polynomial in m and incoming tape
length. No bound on the numerical value of B is used here. -/
theorem ordinary_bound :
    ∃ A d : ℕ, ∀ m B W (mword Bword Dword width : List Bool)
      (s : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B),
      0 < m → 0 < B → mword.length ≤ W → Bword.length ≤ W →
      Dword.length ≤ 6*W+30 → width.length ≤ W →
      W+CodeParametersProgram.fullBudget m B mword.length Bword.length+
        CodeRowsProgram.cost Dword mword width s Q+2  ≤  A*(inputSize m W)^d := by
  obtain ⟨C,e,hC⟩ := CodeParametersProgram.runtime_ordinary
  refine ⟨C*2^e+10000000*9^6+1,e+7,?_⟩
  intro m B W mword Bword Dword width s Q hm hB hmw hBw hDw hb
  let X := inputSize m W
  have hX : 1 ≤ X := by dsimp [X,inputSize]; omega
  have hp0 := hC m B mword.length Bword.length hm hB
  have hp : CodeParametersProgram.fullBudget m B mword.length Bword.length  ≤
      (C*2^e)*X^e := by
    calc
      _  ≤  C*(CodeParametersProgram.setupInput m mword.length Bword.length)^e := by omega
      _  ≤  C*(2*X)^e := by gcongr; dsimp [CodeParametersProgram.setupInput,X,inputSize]; omega
      _ = _ := by rw [mul_pow]; ring
  have hz := serializer_bound hm hB W mword Dword width s Q hmw hDw hb
  change CodeRowsProgram.cost Dword mword width s Q ≤ (10000000*9^6)*X^6 at hz
  have hpe : X^e ≤ X^(e+7) := Nat.pow_le_pow_right hX (by omega)
  have hp6 : X^6 ≤ X^(e+7) := Nat.pow_le_pow_right hX (by omega)
  have hp1 : X ≤ X^(e+7) := by simpa using Nat.pow_le_pow_right hX (by omega : 1 ≤ e+7)
  have hw : W+2 ≤ X := by dsimp [X,inputSize]; omega
  have hp' := hp.trans (Nat.mul_le_mul_left (C*2^e) hpe)
  have hz' := hz.trans (Nat.mul_le_mul_left (10000000*9^6) hp6)
  change _  ≤  (C*2^e+10000000*9^6+1)*X^(e+7)
  nlinarith only [hp',hz',hw.trans hp1]

end SubexponentialSAT.SqrtLog.CodeSetupOuterCost

end OAI.Algorithms

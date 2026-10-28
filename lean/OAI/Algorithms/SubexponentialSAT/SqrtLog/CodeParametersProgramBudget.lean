import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgramUnary

namespace OAI.Algorithms

/-! Ordinary-polynomial cost of the actual sparse-code metadata producer.
The two exhaustive code searches have separate costs; this file accounts
for the fixed arithmetic table and all seven unary materializations. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open LeafParametersProgram.Circuit


def setupInput (m ml Bl : ℕ) : ℕ := m+ml+Bl+16

def prefixEnvelope (m ml Bl : ℕ) : ℕ :=
  iterMajorant prefixCode.length (setupInput m ml Bl)

def setupEnvelope (m ml Bl : ℕ) : ℕ :=
  iterMajorant suffixCode.length (2*prefixEnvelope m ml Bl)

private theorem prefix_scale (m B ml Bl : ℕ) :
    ScaleBound (setupInput m ml Bl) prefixCode (initialModel m B ml Bl) := by
  simp [prefixCode,ScaleBound,scale,setupInput]

private theorem prefix_envelope (m B ml Bl : ℕ) :
    (∀ a, (prefixModel m B ml Bl).len a ≤ prefixEnvelope m ml Bl) ∧
    budget prefixCode (initialModel m B ml Bl) ≤ prefixCode.length*prefixEnvelope m ml Bl := by
  apply budget_majorant prefixCode (initialModel m B ml Bl) (setupInput m ml Bl)
  · intro a
    simp only [initialModel]
    split_ifs <;> dsimp [setupInput] <;> omega
  · exact prefix_scale m B ml Bl

private theorem dimension_le_m {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    SparseCode.dimension m B ≤ m := by
  rw [dimension_eq_size hm hB]
  exact (Nat.size_le.mpr (Nat.lt_two_pow_self)).trans
    ((Nat.div_le_self _ _).trans (Nat.sub_le _ _))

private theorem suffix_scale {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ) :
    ScaleBound (setupInput m ml Bl) suffixCode (middleModel m B ml Bl) := by
  have hr := dimension_eq_size hm hB
  rw [size_eq_log2_odd] at hr
  have hr' : Nat.log 2 (((m-1)/SparseCode.degree m B)+((m-1)/SparseCode.degree m B)+1) =
      SparseCode.dimension m B := by
    simpa [Nat.two_mul,Nat.log2_eq_log_two] using hr.symm
  have hd := dimension_le_m hm hB
  simp [suffixCode,ScaleBound,scale,next,output,value,middleModel,prefixModel,
    prefixCode,result,initialModel,BinaryArithmetic.toNat,BinaryArithmetic.bitVal,
    Nat.log2_eq_log_two,hr',setupInput] ; omega

private theorem envelopes_order (m ml Bl : ℕ) :
    setupInput m ml Bl ≤ prefixEnvelope m ml Bl ∧
    2*prefixEnvelope m ml Bl ≤ setupEnvelope m ml Bl :=
  ⟨le_iterMajorant _ _,le_iterMajorant _ _⟩

private theorem suffix_envelope {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ) :
    (∀ a, (finalModel m B ml Bl).len a ≤ setupEnvelope m ml Bl) ∧
    budget suffixCode (middleModel m B ml Bl) ≤ suffixCode.length*setupEnvelope m ml Bl := by
  have hp := prefix_envelope m B ml Bl
  have ho := envelopes_order m ml Bl
  apply budget_majorant suffixCode (middleModel m B ml Bl) (2*prefixEnvelope m ml Bl)
  · intro a
    by_cases ha : a=9
    · subst a
      simpa only [middleModel,Function.update_self,two_mul] using Nat.add_le_add (hp.1 0) (hp.1 8)
    · have h := hp.1 a
      simpa only [middleModel,Function.update_of_ne ha] using
        h.trans (show prefixEnvelope m ml Bl ≤ 2*prefixEnvelope m ml Bl by omega)
  · apply scaleBound_mono (setupInput m ml Bl) (2*prefixEnvelope m ml Bl)
      (by omega) _ _ (suffix_scale hm hB ml Bl)

private theorem final_values_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ)
    (j : Fin 7) :
    (finalModel m B ml Bl).val (binaryPorts j) ≤ 2*(setupEnvelope m ml Bl)^2 := by
  have hv := final_values hm hB ml Bl
  have he : (finalModel m B ml Bl).val (binaryPorts j)=parameterValues m B j := by
    fin_cases j
    · exact hv.2.1
    · exact hv.2.2.1
    · exact hv.2.2.2.1
    · exact hv.2.2.2.2.1
    · exact hv.2.2.2.2.2.1
    · exact hv.2.2.2.2.2.2.1
    · exact hv.2.2.2.2.2.2.2
  rw [he]
  apply (parameterValues_le hm hB j).trans
  apply Nat.mul_le_mul_left 2
  apply Nat.pow_le_pow_left
  have ho := envelopes_order m ml Bl
  dsimp [setupInput] at ho
  omega

private theorem unary_row_budget {v l Z : ℕ} (hZ : 1 ≤ Z) (hl : l ≤ Z) (hv : v ≤ 2*Z^2) :
    7*l+6+(2*v+(v+1)*(16*l+16)+2*l+6) ≤ 128*Z^3 := by
  have h1 : Z ≤ Z^3 := Nat.le_self_pow (by decide) _
  have h2 : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
  have h0 : 1 ≤ Z^3 := one_le_pow₀ hZ
  calc
    _ ≤ 7*Z+6+(2*(2*Z^2)+(2*Z^2+1)*(16*Z+16)+2*Z+6) := by gcongr
    _ ≤ _ := by nlinarith only [h1,h2,h0]

private theorem unary_envelope {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ) :
    unaryModelBudget (finalModel m B ml Bl) ≤ 896*(setupEnvelope m ml Bl)^3 := by
  let z := finalModel m B ml Bl
  let Z := setupEnvelope m ml Bl
  have hZ : 1 ≤ Z := by
    have ho := envelopes_order m ml Bl
    dsimp [Z,setupInput] at *
    omega
  have hl := (suffix_envelope hm hB ml Bl).1
  have hb (j : Fin 7) :
      7*z.len (binaryPorts j)+6+(2*z.val (binaryPorts j)+
        (z.val (binaryPorts j)+1)*(16*z.len (binaryPorts j)+16)+2*z.len (binaryPorts j)+6) ≤ 128*Z^3 :=
    unary_row_budget hZ (hl _) (final_values_bound hm hB ml Bl j)
  have h9 := hb 0
  have h11 := hb 1
  have h12 := hb 2
  have h15 := hb 3
  have h18 := hb 4
  have h19 := hb 5
  have h21 := hb 6
  simp +decide [binaryPorts] at h9 h11 h12 h15 h18 h19 h21
  change unaryModelBudget z ≤ 896*Z^3
  simp only [unaryModelBudget,unaryPairs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

/-- This bound includes the halt after the actual native metadata command. -/
theorem fullBudget_envelope {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ) :
    fullBudget m B ml Bl+1 ≤
      (prefixCode.length+suffixCode.length+1017)*(setupEnvelope m ml Bl)^3 := by
  let Y := prefixEnvelope m ml Bl
  let Z := setupEnvelope m ml Bl
  have hp := prefix_envelope m B ml Bl
  have hs := suffix_envelope hm hB ml Bl
  have hu := unary_envelope hm hB ml Bl
  have ho := envelopes_order m ml Bl
  have hYZ : Y ≤ Z := by dsimp [Y,Z]; omega
  have hZ : 1 ≤ Z := by dsimp [Y,Z,setupInput] at *; omega
  have hmin : 40*((prefixModel m B ml Bl).len 0+(prefixModel m B ml Bl).len 8+1) ≤ 120*Z := by
    have h0 : (prefixModel m B ml Bl).len 0 ≤ Y := hp.1 0
    have h8 : (prefixModel m B ml Bl).len 8 ≤ Y := hp.1 8
    omega
  have h1 : Z ≤ Z^3 := Nat.le_self_pow (by decide) _
  have h0 : 1 ≤ Z^3 := one_le_pow₀ hZ
  have hpre : budget prefixCode (initialModel m B ml Bl) ≤ prefixCode.length*Z^3 :=
    hp.2.trans (Nat.mul_le_mul_left _ (hYZ.trans h1))
  have hsuf : budget suffixCode (middleModel m B ml Bl) ≤ suffixCode.length*Z^3 :=
    hs.2.trans (Nat.mul_le_mul_left _ h1)
  have hm3 := hmin.trans (Nat.mul_le_mul_left 120 h1)
  change fullBudget m B ml Bl+1 ≤ (prefixCode.length+suffixCode.length+1017)*Z^3
  dsimp only [fullBudget,runtimeBound]
  change unaryModelBudget (finalModel m B ml Bl) ≤ 896*Z^3 at hu
  nlinarith only [hpre,hsuf,hm3,hu,h0]

/-- A fixed ordinary polynomial bounds every arithmetic operation, copy,
comparison and unary output in the metadata producer. Input padding is
charged through ml and Bl. Numeric B does not enter this input measure. -/
theorem runtime_ordinary :
    ∃ C d : ℕ, ∀ m B ml Bl, 0 < m → 0 < B →
      fullBudget m B ml Bl+1 ≤ C*(setupInput m ml Bl)^d := by
  have hepExists : ∃ e : ℕ, e = 6^prefixCode.length := ⟨_, rfl⟩
  have hesExists : ∃ e : ℕ, e = 6^suffixCode.length := ⟨_, rfl⟩
  have hcpExists : ∃ c : ℕ, c = polynomialCoefficient prefixCode.length := ⟨_, rfl⟩
  have hcsExists : ∃ c : ℕ, c = polynomialCoefficient suffixCode.length := ⟨_, rfl⟩
  let ep := Classical.choose hepExists
  let es := Classical.choose hesExists
  let cp := Classical.choose hcpExists
  let cs := Classical.choose hcsExists
  have hep : ep = 6^prefixCode.length := Classical.choose_spec hepExists
  have hes : es = 6^suffixCode.length := Classical.choose_spec hesExists
  have hcp : cp = polynomialCoefficient prefixCode.length := Classical.choose_spec hcpExists
  have hcs : cs = polynomialCoefficient suffixCode.length := Classical.choose_spec hcsExists
  let A := cs*(2*cp)^es
  let E := ep*es
  refine ⟨(prefixCode.length+suffixCode.length+1017)*A^3,E*3,?_⟩
  intro m B ml Bl hm hB
  let X := setupInput m ml Bl
  have hX : 1 ≤ X := by dsimp [X,setupInput]; omega
  have hY : 1 ≤ 2*prefixEnvelope m ml Bl := by
    have h := (envelopes_order m ml Bl).1
    change X ≤ prefixEnvelope m ml Bl at h
    omega
  have hp : prefixEnvelope m ml Bl ≤ cp*X^ep := by
    rw [hcp, hep]
    exact iterMajorant_polynomial _ _ hX
  have hs : setupEnvelope m ml Bl ≤ cs*(2*prefixEnvelope m ml Bl)^es :=
    by
      rw [hcs, hes]
      exact iterMajorant_polynomial _ _ hY
  have hZ : setupEnvelope m ml Bl ≤ A*X^E := by
    calc
      _ ≤ cs*(2*(cp*X^ep))^es := hs.trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hp) _))
      _ = _ := by
        dsimp [A,E]
        rw [show 2*(cp*X^ep)=(2*cp)*X^ep by ring,mul_pow,← pow_mul]
        ring
  calc
    _ ≤ (prefixCode.length+suffixCode.length+1017)*(setupEnvelope m ml Bl)^3 :=
      fullBudget_envelope hm hB ml Bl
    _ ≤ (prefixCode.length+suffixCode.length+1017)*(A*X^E)^3 := by gcongr
    _ = _ := by rw [mul_pow,← pow_mul]; ring

end SubexponentialSAT.SqrtLog.CodeParametersProgram

end OAI.Algorithms

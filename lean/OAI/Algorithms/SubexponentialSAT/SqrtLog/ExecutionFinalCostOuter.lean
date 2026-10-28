import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionFinalCostAlgebra
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramCertificate

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Execution.FinalCost
open SubexponentialSAT.SqrtLog.Statement

/-- The exact measured outer controller, including parser and Main overhead. -/
theorem controller_le_runtimeBound {C A : ℝ} (hC : 1 ≤ C) (hA : 0 ≤ A)
    (d n P S leaves W : ℕ) (hPS : P+S ≤ W)
    (hleaves : (leaves:ℝ) ≤ (2:ℝ)^(129*runtimeScale n)) :
    ((Budget.mk P P S leaves W
      (LeafOuterProgram.MainAdapter.leafLimit W (2*W)
        (Nat.ceil (runtimeBound C A d (3*W+1) n)))).total : ℝ) ≤
      runtimeBound (300019+200002*C*3^d) (A+129) (d+1) W n := by
  let R := Nat.ceil (runtimeBound C A d (3*W+1) n)
  let B := runtimeBound 1 A (d+1) W n
  let V := runtimeBound 1 (A+129) (d+1) W n
  have hC0 : 0 ≤ C := by linarith
  have hAp : 0 ≤ A+129 := by linarith
  have hi : (W:ℝ)+1 ≤ B := Execution.input_le_runtimeBound
    (by norm_num) hA (by omega : 0 < d+1) W n
  have hiv : (W:ℝ)+1 ≤ V := Execution.input_le_runtimeBound
    (by norm_num) hAp (by omega : 0 < d+1) W n
  have hR : (R:ℝ) ≤ 2*(C*3^d)*B := by
    have hsub := Execution.runtimeBound_input_substitution hC0 hA
      (by norm_num : (0:ℝ) ≤ 3) d 1 W (3*W+1) n n
      (by push_cast; linarith) (by rfl)
    have hdeg := Execution.runtimeBound_mono_degree (C:=C*3^d) (A:=A)
      (by positivity) (show d ≤ d+1 by omega) W n
    calc
      _ ≤ 2*runtimeBound C A d (3*W+1) n := Execution.ceil_runtimeBound_le hC hA _ _ _
      _ ≤ 2*runtimeBound (C*3^d) A d W n := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa only [one_mul] using hsub
      _ ≤ 2*runtimeBound (C*3^d) A (d+1) W n := mul_le_mul_of_nonneg_left hdeg (by norm_num)
      _ = _ := by dsimp [B,runtimeBound]; ring
  have hleaf : ((6*W+LeafOuterProgram.MainAdapter.leafLimit W (2*W) R+7:ℕ):ℝ) ≤
      (300014+200002*C*3^d)*B := by
    unfold LeafOuterProgram.MainAdapter.leafLimit
    push_cast
    nlinarith only [hi,hR]
  have hpref : ((P+P+S+5:ℕ):ℝ) ≤ 5*V := by
    have hh : P+P+S+5 ≤ 5*(W+1) := by omega
    exact (show ((P+P+S+5:ℕ):ℝ) ≤ 5*((W:ℝ)+1) by exact_mod_cast hh).trans
      (mul_le_mul_of_nonneg_left hiv (by norm_num))
  have hexp : (2:ℝ)^(129*runtimeScale n)*B=V := by
    have hh := runtimeBound_product 1 129 1 A 0 (d+1) W n
    simpa only [B,V,runtimeBound,pow_zero,mul_one,one_mul,zero_add,add_comm] using hh
  have hcalls : (leaves:ℝ)*((6*W+LeafOuterProgram.MainAdapter.leafLimit W (2*W) R+7:ℕ):ℝ) ≤
      (300014+200002*C*3^d)*V := by
    calc
      _ ≤ (2:ℝ)^(129*runtimeScale n)*((300014+200002*C*3^d)*B) :=
        mul_le_mul hleaves hleaf (Nat.cast_nonneg _) (by positivity)
      _ = (300014+200002*C*3^d)*((2:ℝ)^(129*runtimeScale n)*B) := by ring
      _ = _ := by rw [hexp]
  change ((P+P+S+5+leaves*(6*W+LeafOuterProgram.MainAdapter.leafLimit W (2*W) R+7):ℕ):ℝ) ≤ _
  rw [Nat.cast_add,Nat.cast_mul]
  calc
    _ ≤ 5*V+(300014+200002*C*3^d)*V := add_le_add hpref hcalls
    _ = _ := by dsimp [V,runtimeBound]; ring

/-- Fixed constants are selected before all input sizes and concrete runs. -/
theorem outer_budget_bound {Cp C A : ℝ} (hCp : 0 ≤ Cp) (hC : 1 ≤ C) (hA : 0 ≤ A)
    (q d : ℕ) :
    ∃ Cf Af : ℝ, ∃ df : ℕ, 1 ≤ Cf ∧ 0 < Af ∧ 0 < df ∧
      ∀ L n P S leaves : ℕ,
      (P:ℝ) ≤ Cp*((L:ℝ)+1)^q →
      (S:ℝ) ≤ 3617*((L:ℝ)+1)^2*(2:ℝ)^(130*runtimeScale n) →
      (leaves:ℝ) ≤ (2:ℝ)^(129*runtimeScale n) →
      ((Budget.mk P P S leaves (L+P+S)
        (LeafOuterProgram.MainAdapter.leafLimit (L+P+S) (2*(L+P+S))
          (Nat.ceil (runtimeBound C A d (3*(L+P+S)+1) n)))).total : ℝ) ≤
        runtimeBound Cf Af df L n := by
  let F := 300019+200002*C*3^d
  let H := Cp+3618
  refine ⟨F*H^(d+1),A+129+((d+1:ℕ):ℝ)*130,(q+2)*(d+1),?_,?_,?_,?_⟩
  · have hF : 1 ≤ F := by
      have hh : 0 ≤ 200002*C*3^d := by positivity
      dsimp [F]
      linarith
    have hH : 1 ≤ H := by dsimp [H]; linarith
    exact one_le_mul_of_one_le_of_one_le hF (one_le_pow₀ hH)
  · have hd : (0:ℝ) ≤ ((d+1:ℕ):ℝ) := Nat.cast_nonneg _
    linarith
  · positivity
  · intro L n P S leaves hP hS hleaves
    have hw := state_size_bound hCp q L n P S hP hS
    have hc := controller_le_runtimeBound hC hA d n P S leaves (L+P+S) (by omega) hleaves
    have hs := runtimeBound_substitute (C:=F) (A:=A+129) (H:=H) (B:=130)
      (by dsimp [F]; positivity) (d+1) (q+2) L (L+P+S) n hw
    exact hc.trans hs

end SubexponentialSAT.SqrtLog.Execution.FinalCost

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionRuntime

namespace OAI.Algorithms

/-! Numerical closure for costs of already implemented final controllers. -/
namespace SubexponentialSAT.SqrtLog.Execution.FinalCost
open SubexponentialSAT.SqrtLog.Statement

/-- Includes the exact classifier overhead, setup power, and rounded tail.
All three input words retain their full physical lengths. -/
theorem coreLimit_le_runtimeBound {Ct At : ℝ} (hC : 1 ≤ Ct) (hA : 0 ≤ At)
    (p dt n setup : ℕ) (hdt : 0 < dt)
    (nw Bw bits : List Bool) (tailCost : List Bool → ℕ)
    (hsetup : (setup:ℝ) ≤ (2:ℝ)^runtimeScale n)
    (htail : tailCost bits ≤ Nat.ceil (runtimeBound Ct At dt
      (bits.length+nw.length+Bw.length+1) n)) :
    (LeafOuterProgram.coreLimit setup p nw Bw tailCost bits : ℝ) ≤
      runtimeBound (108+2*Ct) (At+1) (p+dt+1)
        (bits.length+nw.length+Bw.length+1) n := by
  let L := bits.length+nw.length+Bw.length+1
  let R := runtimeBound 1 (At+1) (p+dt+1) L n
  have hAp : 0 ≤ At+1 := by linarith
  have h1 : 1 ≤ R := one_le_runtimeBound (by norm_num) hAp _ _ _
  have hi : (bits.length:ℝ)+1 ≤ R := by
    have hh := Execution.input_le_runtimeBound (C:=1) (by norm_num) hAp
      (show 0 < p+dt+1 by omega) L n
    have hb : (bits.length:ℝ)+1 ≤ (L:ℝ)+1 := by dsimp [L]; push_cast; linarith
    exact hb.trans hh
  have hp : ((L:ℝ)+1)^p ≤ ((L:ℝ)+1)^(p+dt+1) :=
    pow_le_pow_right₀ (by have := Nat.cast_nonneg (α:=ℝ) L; linarith) (by omega)
  have hexp : (2:ℝ)^runtimeScale n ≤ (2:ℝ)^((At+1)*runtimeScale n) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [runtimeScale_nonneg n]
  have hs : (setup:ℝ)*((L:ℝ)+1)^p ≤ R := by
    have hmul := mul_le_mul hsetup hp (by positivity)
      (by positivity : (0:ℝ) ≤ (2:ℝ)^runtimeScale n)
    calc
      _ ≤ (2:ℝ)^runtimeScale n*((L:ℝ)+1)^(p+dt+1) := hmul
      _ ≤ (2:ℝ)^((At+1)*runtimeScale n)*((L:ℝ)+1)^(p+dt+1) :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = R := by dsimp [R,runtimeBound]; ring
  have hrt : runtimeBound Ct At dt L n ≤ Ct*R := by
    have hd := Execution.runtimeBound_mono_degree (A:=At) (show 0 ≤ Ct by linarith)
      (show dt ≤ p+dt+1 by omega) L n
    have ha := runtimeBound_mono_exponent (show 0 ≤ Ct by linarith)
      (show At ≤ At+1 by linarith) (p+dt+1) L n
    calc
      _ ≤ runtimeBound Ct (At+1) (p+dt+1) L n := hd.trans ha
      _ = Ct*R := by dsimp [R,runtimeBound]; ring
  have ht : (tailCost bits:ℝ) ≤ 2*Ct*R := by
    calc
      _ ≤ (Nat.ceil (runtimeBound Ct At dt L n):ℝ) := by exact_mod_cast htail
      _ ≤ 2*runtimeBound Ct At dt L n := Execution.ceil_runtimeBound_le hC hA _ _ _
      _ ≤ 2*(Ct*R) := mul_le_mul_of_nonneg_left hrt (by norm_num)
      _ = _ := by ring
  have hpow : ((bits.length:ℝ)+(nw.length:ℝ)+(Bw.length:ℝ)+2)^p = ((L:ℝ)+1)^p := by
    congr 1
    dsimp [L]
    push_cast
    ring
  unfold LeafOuterProgram.coreLimit
  push_cast
  rw [hpow]
  calc
    _ ≤ (108+2*Ct)*R := by nlinarith only [h1,hi,hs,ht]
    _ = _ := by dsimp [R,L,runtimeBound]; ring

end SubexponentialSAT.SqrtLog.Execution.FinalCost

end OAI.Algorithms

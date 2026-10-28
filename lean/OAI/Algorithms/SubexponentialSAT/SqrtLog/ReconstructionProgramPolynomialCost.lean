import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramCost

namespace OAI.Algorithms

/-! A uniform polynomial bound on the complete primitive CRT program. The
residue-field cardinality is a runtime dimension, as are all tape widths. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Native
open SubexponentialSAT.SubexpLiftRing

def costConstant : ℕ := 10000*1000001^3+1000000

private theorem entry_le (S modulusBits widthTokens : ℕ)
    (hm : modulusBits ≤ S) (hw : widthTokens ≤ S) :
    Entry.budget modulusBits widthTokens ≤ 24*(S+1) := by
  unfold Entry.budget
  omega

private theorem controller_polynomial (S Q J t d : ℕ)
    (hQ : Q ≤ S) (hJ : J ≤ S) (ht : t ≤ S) (hd : d ≤ S)
    (hq : 3^d ≤ S) :
    controllerBudget (d*baseWidth 3 t) J Q (middleBudget Q J t d) + 1 ≤
      2300*((costConstant+1)^4*(S+1)^96)+1 := by
  let T := S+1
  let U := costConstant*T^24
  have hT : 0 < T := by dsimp [T]; omega
  have hS : S ≤ T := by dsimp [T]; omega
  have h124 : T ≤ T^24 := by simpa only [pow_one] using Nat.pow_le_pow_right hT (show 1 ≤ 24 by decide)
  have h224 : T^2 ≤ T^24 := Nat.pow_le_pow_right hT (by decide)
  have h524 : T^5 ≤ T^24 := Nat.pow_le_pow_right hT (by decide)
  have h024 : 1 ≤ T^24 := by simpa only [pow_zero] using Nat.pow_le_pow_right hT (show 0 ≤ 24 by decide)
  have hC : 200000 ≤ costConstant := by
    rw [costConstant]
    exact (show 200000 ≤ 1000000 by decide).trans
      (Nat.le_add_left 1000000 (10000*1000001^3))
  have hC1 : 1 ≤ costConstant := (show 1 ≤ 200000 by decide).trans hC
  have hSU : S ≤ U := by
    calc
      S ≤ T^24 := hS.trans h124
      _ = 1*T^24 := by simp
      _ ≤ U := Nat.mul_le_mul_right _ hC1
  have hlog : Nat.log 2 3 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  have hB : baseWidth 3 t ≤ 2*T := by norm_num [baseWidth, hlog]; dsimp [T]; omega
  have hB1 : baseWidth 3 t+1 ≤ 2*T := by norm_num [baseWidth, hlog]; dsimp [T]; omega
  have hd1 : d+1 ≤ T := by dsimp [T]; omega
  have hW : d*baseWidth 3 t ≤ U := by
    calc
      _ ≤ T*(2*T) := Nat.mul_le_mul (hd.trans hS) hB
      _ = 2*T^2 := by ring
      _ ≤ U := Nat.mul_le_mul ((show 2 ≤ 200000 by decide).trans hC) h224
  have hmul : HornerProgram.Services.mulBudget (baseWidth 3 t) d ≤ U := by
    calc
      _ ≤ 50000*(d+1)^3*(baseWidth 3 t+1)^2 := HornerProgram.Services.mulBudget_polynomial _ _
      _ ≤ 50000*T^3*(2*T)^2 := by gcongr
      _ = 200000*T^5 := by ring
      _ ≤ U := Nat.mul_le_mul hC h524
  have hadd : HornerProgram.Services.addBudget (baseWidth 3 t) d ≤ U := by
    calc
      _ ≤ 50000*(d+1)^3*(baseWidth 3 t+1)^2 := HornerProgram.Services.addBudget_polynomial _ _
      _ ≤ 50000*T^3*(2*T)^2 := by gcongr
      _ = 200000*T^5 := by ring
      _ ≤ U := Nat.mul_le_mul hC h524
  have hlocal : CRTLocalProgram.Native.budget Q Q (3^d) t d J ≤ U := by
    calc
      _ ≤ 10000*1000001^3*(S+1)^24 := CRTLocalProgram.Native.budget_polynomial S Q Q (3^d) t d J
        hQ hQ hq ht hd hJ
      _ ≤ U := Nat.mul_le_mul_right _ (by
        rw [costConstant]
        exact Nat.le_add_right (10000*1000001^3) 1000000)
  have hmain := reconstructionBudget_le Q J (d*baseWidth 3 t)
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d)
    (CRTLocalProgram.Native.budget Q Q (3^d) t d J) U
    (hQ.trans hSU) (hJ.trans hSU) hW hmul hadd hlocal
  have hU1 : U+1 ≤ (costConstant+1)*T^24 := by
    calc
      U+1 ≤ U+T^24 := Nat.add_le_add_left h024 U
      _ = _ := by dsimp [U]; ring
  have hpow : (U+1)^4 ≤ (costConstant+1)^4*T^96 := by
    calc
      _ ≤ ((costConstant+1)*T^24)^4 := Nat.pow_le_pow_left hU1 4
      _ = _ := by ring
  have hctrl := hmain.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2300 hpow) 1)
  simpa only [T, middleBudget] using hctrl

theorem budget_polynomial (S Q J t d modulusBits widthTokens : ℕ)
    (hQ : Q ≤ S) (hJ : J ≤ S) (ht : t ≤ S) (hd : d ≤ S)
    (hq : 3^d ≤ S) (hm : modulusBits ≤ S) (hw : widthTokens ≤ S) :
    budget Q J t d modulusBits widthTokens + 1 ≤
      2400*(costConstant+1)^4*(S+1)^96+1 := by
  let T := S+1
  have hT : 0 < T := by dsimp [T]; omega
  have h196 : T ≤ T^96 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hT (show 1 ≤ 96 by decide)
  have hCpow : 1 ≤ (costConstant+1)^4 := by
    simpa only [pow_zero] using Nat.pow_le_pow_right
      (Nat.succ_pos costConstant) (show 0 ≤ 4 by decide)
  have hscale : 24 ≤ 100*(costConstant+1)^4 :=
    (show 24 ≤ 100 by decide).trans (Nat.mul_le_mul_left 100 hCpow)
  have hentry : Entry.budget modulusBits widthTokens ≤ 24*T :=
    entry_le S modulusBits widthTokens hm hw
  have hentry' : Entry.budget modulusBits widthTokens ≤
      100*(costConstant+1)^4*T^96 :=
    hentry.trans (Nat.mul_le_mul hscale h196)
  have hctrl := controller_polynomial S Q J t d hQ hJ ht hd hq
  calc
    budget Q J t d modulusBits widthTokens + 1 =
        Entry.budget modulusBits widthTokens +
          (controllerBudget (d*baseWidth 3 t) J Q (middleBudget Q J t d) + 1) := by
      unfold budget
      exact Nat.add_assoc _ _ _
    _ ≤ 100*(costConstant+1)^4*T^96 + (2300*((costConstant+1)^4*T^96)+1) :=
      Nat.add_le_add hentry' hctrl
    _ = 2400*(costConstant+1)^4*(S+1)^96+1 := by dsimp [T]; ring

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

end OAI.Algorithms

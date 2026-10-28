import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramNative

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.SubexpLiftRing

theorem localBudget_le_uniform (S nodes index e t J Km Ka Kp Kap W V : ℕ)
    (hn : nodes ≤ S) (hi : index ≤ S) (he : e ≤ S) (ht : t ≤ S) (hJ : J ≤ S)
    (hm : Km ≤ S) (ha : Ka ≤ S) (hp : Kp ≤ S) (hap : Kap ≤ S)
    (hw : W ≤ S) (hv : V ≤ S) :
    localBudget nodes index e t J Km Ka Kp Kap W V ≤ 10000*(S+1)^3 := by
  calc
    _ ≤ localBudget S S S S S S S S S S S := by
      unfold localBudget initializationBudget includeBudget preparationBudget
        inverseConstantsBudget inverseBudget correctionBudget
      gcongr
    _ ≤ _ := by
      unfold localBudget initializationBudget includeBudget preparationBudget
        inverseConstantsBudget inverseBudget correctionBudget
      ring_nf
      omega

namespace Native

theorem budget_mono_index (nodes q t d J i j : ℕ) (h : i ≤ j) :
    budget nodes i q t d J ≤ budget nodes j q t d J := by
  unfold budget localBudget initializationBudget preparationBudget
  gcongr

/-- A deliberately coarse uniform polynomial bound in every runtime size. -/
theorem budget_polynomial (S nodes index q t d J : ℕ)
    (hn : nodes ≤ S) (hi : index ≤ S) (hq : q ≤ S)
    (ht : t ≤ S) (hd : d ≤ S) (hJ : J ≤ S) :
    budget nodes index q t d J ≤ 10000*1000001^3*(S+1)^24 := by
  let T := S+1
  let K := 1000000*T^8
  have hT : 0 < T := by dsimp [T]; omega
  have hS : S ≤ T := by dsimp [T]; omega
  have h18 : T ≤ T^8 := by simpa only [pow_one] using Nat.pow_le_pow_right hT (show 1 ≤ 8 by decide)
  have h28 : T^2 ≤ T^8 := Nat.pow_le_pow_right hT (by decide)
  have h38 : T^3 ≤ T^8 := Nat.pow_le_pow_right hT (by decide)
  have h48 : T^4 ≤ T^8 := Nat.pow_le_pow_right hT (by decide)
  have h58 : T^5 ≤ T^8 := Nat.pow_le_pow_right hT (by decide)
  have h08 : 1 ≤ T^8 := by simpa only [pow_zero] using Nat.pow_le_pow_right hT (show 0 ≤ 8 by decide)
  have hlog : Nat.log 2 3 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  have hB : baseWidth 3 t ≤ 2*T := by norm_num [baseWidth, hlog]; dsimp [T]; omega
  have hB1 : baseWidth 3 t+1 ≤ 2*T := by norm_num [baseWidth, hlog]; dsimp [T]; omega
  have hd1 : d+1 ≤ T := by dsimp [T]; omega
  have hJ1 : J+1 ≤ T := by dsimp [T]; omega
  have hdT : d ≤ T := hd.trans hS
  have hJT : J ≤ T := hJ.trans hS
  have hKm : HornerProgram.Services.mulBudget (baseWidth 3 t) d ≤ K := by
    calc
      _ ≤ 50000*(d+1)^3*(baseWidth 3 t+1)^2 := HornerProgram.Services.mulBudget_polynomial _ _
      _ ≤ 50000*T^3*(2*T)^2 := by gcongr
      _ ≤ K := by dsimp [K]; ring_nf; omega
  have hKa : HornerProgram.Services.addBudget (baseWidth 3 t) d ≤ K := by
    calc
      _ ≤ 50000*(d+1)^3*(baseWidth 3 t+1)^2 := HornerProgram.Services.addBudget_polynomial _ _
      _ ≤ 50000*T^3*(2*T)^2 := by gcongr
      _ ≤ K := by dsimp [K]; ring_nf; omega
  have hKp : DensePolynomialProgram.nativeMulBudget J d (baseWidth 3 t) ≤ K := by
    calc
      _ ≤ 100000*(J+1)^3*(d+1)^3*(baseWidth 3 t+1)^2 := DensePolynomialProgram.nativeMulBudget_polynomial _ _ _
      _ ≤ 100000*T^3*T^3*(2*T)^2 := by gcongr
      _ ≤ K := by dsimp [K]; ring_nf; omega
  have hKap : DensePolynomialProgram.AddService.budget d (baseWidth 3 t) J J ≤ K := by
    calc
      _ ≤ 7000*(T*(T+T)+1)*(2*T)^2+1+13*T*(2*T)*(T+T)+16 := by
        unfold DensePolynomialProgram.AddService.budget
        gcongr
      _ ≤ K := by dsimp [K]; ring_nf; omega
  have hW : d*baseWidth 3 t ≤ K := by
    calc
      _ ≤ T*(2*T) := Nat.mul_le_mul hdT hB
      _ ≤ K := by dsimp [K]; ring_nf; omega
  have hV : J*(d*baseWidth 3 t) ≤ K := by
    calc
      _ ≤ T*(T*(2*T)) := Nat.mul_le_mul hJT (Nat.mul_le_mul hdT hB)
      _ ≤ K := by dsimp [K]; ring_nf; omega
  have hSK : S ≤ K := by dsimp [K]; omega
  have hmain := localBudget_le_uniform K nodes index (q-2) t J
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d)
    (DensePolynomialProgram.nativeMulBudget J d (baseWidth 3 t))
    (DensePolynomialProgram.AddService.budget d (baseWidth 3 t) J J)
    (d*baseWidth 3 t) (J*(d*baseWidth 3 t))
    (hn.trans hSK) (hi.trans hSK) (by omega) (ht.trans hSK) (hJ.trans hSK)
    hKm hKa hKp hKap hW hV
  change budget nodes index q t d J ≤ _ at hmain
  calc
    _ ≤ 10000*(K+1)^3 := hmain
    _ ≤ 10000*(1000001*T^8)^3 := by gcongr; dsimp [K]; omega
    _ = _ := by dsimp [T]; ring

end Native
end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms

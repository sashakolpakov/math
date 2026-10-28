import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramFactor

namespace OAI.Algorithms

/-! One included-node update of the truncated local cofactor. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def includeNodeCommand (scalarMultiply scalarAdd polynomialMultiply : Code) : Code :=
  .seq (replace 240 223) (.seq (clear 240)
    (.seq (linearFactorCommand scalarMultiply scalarAdd)
      (.seq (replace 223 240) (.seq (clear 223) (.seq (replace 243 246)
        (.seq (nativeRepeat (binaryStep polynomialMultiply)) (clear 241)))))))

def includeBudget (Km Ka Kp W V J : ℕ) : ℕ :=
  Km+Ka+102*W+113+220*(J+1)*(W+1)+(J+1)*(Kp+50*V+50)

theorem includeNodeCommand_run {C P : Type*} (base : Store)
    (encodeC : C → List Bool) (encodeP : P → List Bool)
    (sm sa pm : Code) (cm ca : C → C → C) (mulP : P → P → P)
    (Km Ka Kp W V J : ℕ) (one minusOne : C) (linear : C → P)
    (hsm : ServiceSpec base encodeC sm cm Km) (hsa : ServiceSpec base encodeC sa ca Ka)
    (hpm : ServiceSpec base encodeP pm mulP Kp)
    (hcwidth : ∀ a, (encodeC a).length = W) (hpwidth : ∀ a, (encodeP a).length ≤ V)
    (hlinear : ∀ a, encodeP (linear a) = DensePolynomialProgram.Constructor.Counter.paddedBits
      W (encodeC a) (encodeC one) J)
    (s : Store) (theta other : C) (acc : P) (hf : LowFrame base s)
    (htheta : s 213 = encodeC theta) (hother : s 218 = encodeC other)
    (hone : s 207 = encodeC one) (hminus : s 211 = encodeC minusOne)
    (hJ : s 243 = List.replicate J true) (hzero : s 104 = List.replicate W false)
    (h100 : s 100 = []) (h101 : s 101 = []) (h102 : s 102 = [])
    (h107 : s 107 = []) (h108 : s 108 = []) (h120 : s 120 = [])
    (h205 : s 205 = []) (h219 : s 219 = []) (h223 : s 223 = [])
    (h240 : s 240 = encodeP acc) (h241 : s 241 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = []) :
    ExecutesIn (includeNodeCommand sm sa pm) (includeBudget Km Ka Kp W V J) s
      (Function.update s 240 (encodeP
        ((fun p => mulP p (linear (differenceValue cm ca theta other minusOne)))^[J] acc))) := by
  let factor := linear (differenceValue cm ca theta other minusOne)
  let value := (fun p => mulP p factor)^[J] acc
  let s1 := Function.update s 223 (encodeP acc)
  let s2 := Function.update s1 240 []
  let s3 := Function.update s2 241 (encodeP factor)
  let s4 := Function.update s3 240 (encodeP acc)
  let s5 := Function.update s 241 (encodeP factor)
  let s6 := Function.update s5 246 (List.replicate J true)
  let s7 := Function.update s5 240 (encodeP value)
  have hf1 : LowFrame base s1 := lowFrame_update hf 223 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf1 240 (by decide) _
  have hf5 : LowFrame base s5 := lowFrame_update hf 241 (by decide) _
  have hf6 : LowFrame base s6 := lowFrame_update hf5 246 (by decide) _
  have h1 : ExecutesIn (replace 240 223) (9*V+8) s s1 := by
    simpa [s1, h240] using replace_bounded s 240 223 V (by decide) (by decide) (by decide)
      h120 (by simpa [h240] using hpwidth acc) (by simp [h223])
  have h2 : ExecutesIn (clear 240) (2*V+3) s1 s2 := by
    have h := clear_run 240 s1
    apply h.mono
    simp [s1, h240]
    have hw := hpwidth acc
    omega
  have h3 : ExecutesIn (linearFactorCommand sm sa)
      (Km+Ka+102*W+113+220*(J+1)*(W+1)) s2 s3 := by
    have h := linearFactorCommand_run base encodeC sm sa cm ca Km Ka W J hsm hsa hcwidth
      s2 theta other one minusOne hf2
      (by simp [s2, s1, htheta]) (by simp [s2, s1, hother])
      (by simp [s2, s1, hone]) (by simp [s2, s1, hminus])
      (by simp [s2, s1, hJ]) (by simp [s2, s1, hzero])
      (by simp [s2, s1, h100]) (by simp [s2, s1, h101])
      (by simp [s2, s1, h102]) (by simp [s2, s1, h107])
      (by simp [s2, s1, h108]) (by simp [s2, s1, h120])
      (by simp [s2, s1, h205]) (by simp [s2, s1, h219])
      (by simp [s2]) (by simp [s2, s1, h241])
      (by simp [s2, s1, h244]) (by simp [s2, s1, h245])
    simpa only [s3, factor, hlinear] using h
  have h4 : ExecutesIn (replace 223 240) (9*V+8) s3 s4 := by
    simpa [s4, s3, s2, s1] using replace_bounded s3 223 240 V
      (by decide) (by decide) (by decide) (by simp [s3, s2, s1, h120])
      (by simpa [s3, s2, s1] using hpwidth acc) (by simp [s3, s2])
  have h5 : ExecutesIn (clear 223) (2*V+3) s4 s5 := by
    have h := clear_run 223 s4
    have he : Function.update s4 223 [] = s5 := by
      funext i
      by_cases hi : i = 223 <;> by_cases hj : i = 240 <;>
        simp [s5, s4, s3, s2, s1, Function.update_apply, hi, hj, h223, h240]
    rw [he] at h
    apply h.mono
    simp [s4, s3, s2, s1]
    have hw := hpwidth acc
    omega
  have h6 : ExecutesIn (replace 243 246) (7*J+8) s5 s6 := by
    simpa [s6, s5, hJ, h246] using replace_run s5 243 246 (by decide) (by decide) (by decide)
      (by simp [s5, h120])
  have h7 : ExecutesIn (nativeRepeat (binaryStep pm)) (J*(Kp+8*V+11)+2) s6 s7 := by
    have h := binary_repeat_state base encodeP pm mulP Kp V hpm hpwidth s6 factor acc hf6
      (by simp [s6, s5, h240]) (by simp [s6, s5])
      (by simp [s6, s5, h244]) (by simp [s6, s5, h245])
    have hc : (s6 246).length = J := by simp [s6]
    rw [hc] at h
    have he : Function.update (Function.update s6 240 (encodeP value)) 246 [] = s7 := by
      funext i
      by_cases hi : i = 240 <;> by_cases hj : i = 246 <;>
        simp [s7, s6, s5, Function.update_apply, hi, hj, h246]
    change ExecutesIn _ _ s6 (Function.update (Function.update s6 240 (encodeP value)) 246 []) at h
    rw [he] at h
    exact h
  have h8 : ExecutesIn (clear 241) (2*V+3) s7 (Function.update s 240 (encodeP value)) := by
    have h := clear_run 241 s7
    have he : Function.update s7 241 [] = Function.update s 240 (encodeP value) := by
      funext i
      by_cases hi : i = 241 <;> simp [s7, s5, Function.update_apply, hi, h241]
    rw [he] at h
    apply h.mono
    simp [s7, s5]
    have hw := hpwidth factor
    omega
  apply (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq h8))))))).mono
  dsimp [includeBudget]
  nlinarith

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramHorner
import OAI.Algorithms.SubexponentialSAT.SubexpLocalCRTSetup

namespace OAI.Algorithms

/-! Native residue-power preparation with dynamic extension degree and ring
precision. Stack 209 contains a unary residue-size-minus-two exponent;
stack 212 independently contains the unary ring precision. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def seedCommand (multiply : Code) : Code :=
  replace 207 240 ;; replace 205 241 ;; replace 209 246 ;;
    nativeRepeat (binaryStep multiply) ;; replace 240 208

def seedState {C : Type*} (s : Store) (encode : C → List Bool) (a b : C) : Store :=
  Function.update (Function.update (Function.update s 240 (encode b)) 241 (encode a))
    208 (encode b)

theorem seedCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply : Code) (mulOp : C → C → C) (K W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp K)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (a one : C) (hf : LowFrame base s)
    (ha : s 205 = encode a) (hone : s 207 = encode one)
    (h120 : s 120 = []) (h208 : s 208 = [])
    (h240 : s 240 = []) (h241 : s 241 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = []) :
    ExecutesIn (seedCommand multiply)
      (((s 209).length + 1) * (K + 50 * W + 100)) s
      (seedState s encode a ((fun x => mulOp x a)^[(s 209).length] one)) := by
  let b := ((fun x => mulOp x a)^[(s 209).length] one)
  let s1 := Function.update s 240 (encode one)
  let s2 := Function.update s1 241 (encode a)
  let s3 := Function.update s2 246 (s 209)
  let s4 := Function.update s2 240 (encode b)
  have hf1 : LowFrame base s1 := lowFrame_update hf 240 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf1 241 (by decide) _
  have hf3 : LowFrame base s3 := lowFrame_update hf2 246 (by decide) _
  have h1 : ExecutesIn (replace 207 240) (9 * W + 8) s s1 := by
    simpa [s1, hone] using replace_bounded s 207 240 W
      (by decide) (by decide) (by decide) h120
      (by simpa [hone] using hwidth one) (by simp [h240])
  have h2 : ExecutesIn (replace 205 241) (9 * W + 8) s1 s2 := by
    simpa [s1, s2, ha] using replace_bounded s1 205 241 W
      (by decide) (by decide) (by decide) (by simp [s1, h120])
      (by simpa [s1, ha] using hwidth a) (by simp [s1, h241])
  have h3 : ExecutesIn (replace 209 246) (7 * (s 209).length + 8) s2 s3 := by
    simpa [s3, s2, s1, h246] using replace_run s2 209 246
      (by decide) (by decide) (by decide) (by simp [s2, s1, h120])
  have h4 : ExecutesIn (nativeRepeat (binaryStep multiply))
      ((s 209).length * (K + 8 * W + 11) + 2) s3 s4 := by
    have h := binary_repeat_state base encode multiply mulOp K W hm hwidth
      s3 a one hf3 (by simp [s3, s2, s1]) (by simp [s3, s2])
      (by simp [s3, s2, s1, h244]) (by simp [s3, s2, s1, h245])
    have hc : (s3 246).length = (s 209).length := by simp [s3]
    rw [hc] at h
    have he : Function.update (Function.update s3 240 (encode b)) 246 [] = s4 := by
      funext i
      by_cases hi : i = 240 <;> by_cases hj : i = 246 <;>
        simp [s4, s3, s2, s1, Function.update_apply, hi, hj, h246]
    change ExecutesIn _ _ s3 (Function.update (Function.update s3 240 (encode b)) 246 []) at h
    rw [he] at h
    exact h
  have h5 : ExecutesIn (replace 240 208) (9 * W + 8) s4 (seedState s encode a b) := by
    have h := replace_bounded s4 240 208 W
      (by decide) (by decide) (by decide) (by simp [s4, s2, s1, h120])
      (by simpa [s4] using hwidth b) (by simp [s4, s2, s1, h208])
    have he : Function.update s4 208 (s4 240) = seedState s encode a b := by
      funext i
      by_cases hi : i = 240 <;> by_cases hj : i = 241 <;> by_cases hk : i = 208 <;>
        simp [s4, s2, s1, seedState, hi, hj, hk]
    rw [he] at h
    exact h
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  apply h.mono
  nlinarith

/-- The remaining scalar inverse stages: form the residue defect, then run
the precision-many geometric recurrence. Every operator is a fixed command. -/
def defectCommand (multiply add : Code) : Code :=
  binaryStep multiply ;; replace 211 241 ;; binaryStep multiply ;;
    replace 207 241 ;; binaryStep add ;; replace 240 222

def repairCommand (multiply add : Code) : Code :=
  replace 104 240 ;; replace 222 241 ;; replace 207 220 ;; replace 212 246 ;;
    hornerCommand multiply add ;; replace 208 241 ;; binaryStep multiply ;;
    replace 240 208 ;;
    SubexpLocalCRTSetup.clearMany [220, 222, 240, 241]

def inverseCommand (multiply add : Code) : Code :=
  seedCommand multiply ;; defectCommand multiply add ;; repairCommand multiply add

def inverseProgram (multiply add : Code) := compiled (inverseCommand multiply add) 205 208

def inverseValue {C : Type*} (mulOp addOp : C → C → C)
    (zero one minusOne a : C) (exponent precision : ℕ) : C :=
  let b := ((fun x => mulOp x a)^[exponent]) one
  let z := addOp (mulOp (mulOp b a) minusOne) one
  mulOp ((hornerValue mulOp addOp z one)^[precision] zero) b

theorem inverseValue_decode {C A : Type*} [CommRing A]
    (decode : C → A) (mulOp addOp : C → C → C)
    (hm : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (ha : ∀ a b, decode (addOp a b) = decode a + decode b)
    (zero one minusOne a : C)
    (hz : decode zero = 0) (ho : decode one = 1) (hn : decode minusOne = -1)
    (q precision : ℕ) :
    decode (inverseValue mulOp addOp zero one minusOne a (q-2) precision) =
      (SubexponentialSAT.SubexpResidueInverse.inverseWithCost q precision (decode a)).1 := by
  rw [SubexponentialSAT.SubexpResidueInverse.inverseWithCost_value]
  simp only [inverseValue, hm, hornerValue_decode decode mulOp addOp hm ha _ one zero ho hz,
    iterate_mul_decode decode mulOp hm, ho, one_mul, ha, hn,
    SubexponentialSAT.NilpotentDefect.geometricInverse]
  have he : decode a ^ (q - 2) * decode a * -1 + 1 = 1 - decode a * decode a ^ (q - 2) := by ring
  rw [he, mul_comm]

theorem inverseValue_correct {C A E : Type*} [CommRing A] [Field E] [Fintype E]
    (decode : C → A) (mulOp addOp : C → C → C)
    (hm : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (ha : ∀ a b, decode (addOp a b) = decode a + decode b)
    (zero one minusOne a : C)
    (hz : decode zero = 0) (ho : decode one = 1) (hn : decode minusOne = -1)
    (rho : A →+* E) (q : ℕ) (hq : Fintype.card E = q)
    (pi : A) (precision : ℕ) (hpi : pi ^ precision = 0)
    (hker : ∀ x, rho x = 0 → pi ∣ x) (hne : rho (decode a) ≠ 0) :
    decode (inverseValue mulOp addOp zero one minusOne a (q-2) precision) * decode a = 1 := by
  rw [inverseValue_decode decode mulOp addOp hm ha zero one minusOne a hz ho hn]
  exact SubexponentialSAT.SubexpResidueInverse.inverseWithCost_correct rho q hq pi precision hpi hker _ hne

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms

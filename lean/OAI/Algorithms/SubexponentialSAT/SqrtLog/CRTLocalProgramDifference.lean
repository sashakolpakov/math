import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramCall

namespace OAI.Algorithms

/-! A physical inverse builder for a difference of two supplied nodes. The
residue exponent and nilpotence precision are the independent runtime inputs
209 and 212; no loop enumerates the lifted ring. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def differenceCommand (multiply add : Code) : Code :=
  .seq (callAt multiply 218 211 219) (.seq (callAt add 213 219 205) (clear 219))

def differenceInverseCommand (multiply add : Code) : Code :=
  .seq (differenceCommand multiply add) (.seq (inverseCommand multiply add) (clear 205))

def differenceValue {C : Type*} (mulOp addOp : C → C → C) (theta other minusOne : C) : C :=
  addOp theta (mulOp other minusOne)

theorem differenceCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka) (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (theta other minusOne : C) (hf : LowFrame base s)
    (htheta : s 213 = encode theta) (hother : s 218 = encode other)
    (hminus : s 211 = encode minusOne) (h120 : s 120 = []) (h205 : s 205 = [])
    (h219 : s 219 = []) (h240 : s 240 = []) (h241 : s 241 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn (differenceCommand multiply add) (Km+Ka+100*W+110) s
      (Function.update s 205 (encode (differenceValue mulOp addOp theta other minusOne))) := by
  let neg := mulOp other minusOne
  let delta := addOp theta neg
  let s1 := Function.update s 219 (encode neg)
  let s2 := Function.update s1 205 (encode delta)
  have hf1 : LowFrame base s1 := lowFrame_update hf 219 (by decide) _
  have h1 : ExecutesIn (callAt multiply 218 211 219) (Km+40*W+50) s s1 :=
    callAt_run base encode multiply mulOp Km W hm hwidth s other minusOne 218 211 219
      (by decide) (by decide) (by decide) hf hother hminus h120 h240 h241 h244 h245
      (by simp [h219])
  have h2 : ExecutesIn (callAt add 213 219 205) (Ka+40*W+50) s1 s2 :=
    callAt_run base encode add addOp Ka W ha hwidth s1 theta neg 213 219 205
      (by decide) (by decide) (by decide) hf1 (by simp [s1, htheta]) (by simp [s1])
      (by simp [s1, h120]) (by simp [s1, h240]) (by simp [s1, h241])
      (by simp [s1, h244]) (by simp [s1, h245]) (by simp [s1, h205])
  have h3 : ExecutesIn (clear 219) (2*W+3) s2 (Function.update s 205 (encode delta)) := by
    have h := clear_run 219 s2
    have he : Function.update s2 219 [] = Function.update s 205 (encode delta) := by
      funext i
      by_cases hi : i = 219 <;> simp [s2, s1, Function.update_apply, hi, h219]
    rw [he] at h
    apply h.mono
    simp [s2, s1]
    have hw := hwidth neg
    omega
  exact (h1.seq (h2.seq h3)).mono (by omega)

theorem differenceInverseCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka) (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (theta other zero one minusOne : C) (hf : LowFrame base s)
    (htheta : s 213 = encode theta) (hother : s 218 = encode other)
    (hzero : s 104 = encode zero) (hone : s 207 = encode one)
    (hminus : s 211 = encode minusOne) (h120 : s 120 = [])
    (h205 : s 205 = []) (h208 : s 208 = []) (h219 : s 219 = [])
    (h220 : s 220 = []) (h222 : s 222 = []) (h240 : s 240 = []) (h241 : s 241 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = []) :
    ExecutesIn (differenceInverseCommand multiply add)
      (inverseBudget (s 209).length (s 212).length Km Ka W + Km+Ka+102*W+113) s
      (Function.update s 208 (encode (inverseValue mulOp addOp zero one minusOne
        (differenceValue mulOp addOp theta other minusOne) (s 209).length (s 212).length))) := by
  let delta := differenceValue mulOp addOp theta other minusOne
  let v := inverseValue mulOp addOp zero one minusOne delta (s 209).length (s 212).length
  let s1 := Function.update s 205 (encode delta)
  let s2 := Function.update s1 208 (encode v)
  have h1 : ExecutesIn (differenceCommand multiply add) (Km+Ka+100*W+110) s s1 :=
    differenceCommand_run base encode multiply add mulOp addOp Km Ka W hm ha hwidth
      s theta other minusOne hf htheta hother hminus h120 h205 h219 h240 h241 h244 h245
  have h2 : ExecutesIn (inverseCommand multiply add)
      (inverseBudget (s 209).length (s 212).length Km Ka W) s1 s2 := by
    have h := inverseCommand_run base encode multiply add mulOp addOp Km Ka W hm ha hwidth
      s1 delta zero one minusOne (lowFrame_update hf 205 (by decide) _)
      (by simp [s1]) (by simp [s1, hzero]) (by simp [s1, hone]) (by simp [s1, hminus])
      (by simp [s1, h120]) (by simp [s1, h208]) (by simp [s1, h220]) (by simp [s1, h222])
      (by simp [s1, h240]) (by simp [s1, h241]) (by simp [s1, h244])
      (by simp [s1, h245]) (by simp [s1, h246])
    simpa only [s2, s1, Function.update_of_ne (show (209 : Fin 256) ≠ 205 by decide),
      Function.update_of_ne (show (212 : Fin 256) ≠ 205 by decide)] using h
  have h3 : ExecutesIn (clear 205) (2*W+3) s2 (Function.update s 208 (encode v)) := by
    have h := clear_run 205 s2
    have he : Function.update s2 205 [] = Function.update s 208 (encode v) := by
      funext i
      by_cases hi : i = 205 <;> simp [s2, s1, Function.update_apply, hi, h205]
    rw [he] at h
    apply h.mono
    simp [s2, s1]
    have hw := hwidth delta
    omega
  exact (h1.seq (h2.seq h3)).mono (by omega)

theorem differenceValue_decode {C A : Type*} [Ring A]
    (decode : C → A) (mulOp addOp : C → C → C)
    (hm : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (ha : ∀ a b, decode (addOp a b) = decode a + decode b)
    (theta other minusOne : C) (hn : decode minusOne = -1) :
    decode (differenceValue mulOp addOp theta other minusOne) = decode theta - decode other := by
  simp [differenceValue, ha, hm, hn, sub_eq_add_neg]

theorem differenceInverse_correct {C A E : Type*} [CommRing A] [Field E] [Fintype E]
    (decode : C → A) (mulOp addOp : C → C → C)
    (hm : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (ha : ∀ a b, decode (addOp a b) = decode a + decode b)
    (theta other zero one minusOne : C)
    (hz : decode zero = 0) (ho : decode one = 1) (hn : decode minusOne = -1)
    (rho : A →+* E) (q : ℕ) (hq : Fintype.card E = q)
    (pi : A) (precision : ℕ) (hpi : pi^precision = 0)
    (hker : ∀ x, rho x = 0 → pi ∣ x)
    (hne : rho (decode theta) ≠ rho (decode other)) :
    decode (inverseValue mulOp addOp zero one minusOne
      (differenceValue mulOp addOp theta other minusOne) (q-2) precision) *
        (decode theta - decode other) = 1 := by
  have hd := differenceValue_decode decode mulOp addOp hm ha theta other minusOne hn
  have hnonzero : rho (decode (differenceValue mulOp addOp theta other minusOne)) ≠ 0 := by
    rw [hd, map_sub]
    exact sub_ne_zero.mpr hne
  have h := inverseValue_correct decode mulOp addOp hm ha zero one minusOne
    (differenceValue mulOp addOp theta other minusOne) hz ho hn rho q hq pi precision hpi hker hnonzero
  simpa only [hd] using h

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms

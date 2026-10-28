import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgramNatural

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update callAt callAt_run)

/-- Inputs253/254 are retained. Caches249/250/251 hold zero/one/minus-one.
Only output255 changes;246/247/248 and native service scratch start and end empty. -/
def signedCommand (multiply add : Code) : Code :=
  .seq (copy 253 246) (.seq (naturalCommand add)
    (.seq (copy 247 255) (.seq (clear 247) (.seq (copy 254 246)
      (.seq (naturalCommand add) (.seq (callAt multiply 247 251 247)
        (.seq (callAt add 255 247 255) (clear 247))))))))

def signedValue {C : Type*} (mul add : C → C → C) (zero one minusOne : C)
    (positive negative : List Bool) : C :=
  add (naturalValue add zero one positive) (mul (naturalValue add zero one negative) minusOne)

def signedBudget (bits Km Ka W : ℕ) : ℕ :=
  bits * (2 * (Ka + 40 * W + 50) + 10) + Km + Ka + 123 * W + 151

theorem signedValue_decode {C A : Type*} [Ring A] (decode : C → A)
    (mul add : C → C → C)
    (hm : ∀ x y, decode (mul x y) = decode x * decode y)
    (ha : ∀ x y, decode (add x y) = decode x + decode y)
    (zero one minusOne : C) (hz : decode zero = 0) (ho : decode one = 1)
    (hn : decode minusOne = -1) (positive negative : List Bool) :
    decode (signedValue mul add zero one minusOne positive negative) =
      (((BinaryArithmetic.toNat positive : ℤ) - (BinaryArithmetic.toNat negative : ℤ) : ℤ) : A) := by
  simp [signedValue, hm, ha, naturalValue_decode decode add ha zero one hz ho,
    hn, sub_eq_add_neg]

theorem signedCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka) (hw : ∀ a, (encode a).length ≤ W)
    (s : Store) (zero one minusOne : C) (hf : LowFrame base s) (hc : Clean s)
    (hz : s 249 = encode zero) (ho : s 250 = encode one) (hn : s 251 = encode minusOne)
    (h246 : s 246 = []) (h247 : s 247 = []) (h248 : s 248 = []) (h255 : s 255 = []) :
    ExecutesIn (signedCommand multiply add)
      (signedBudget ((s 253).length + (s 254).length) Km Ka W) s
      (Function.update s 255 (encode (signedValue mulOp addOp zero one minusOne (s 253) (s 254)))) := by
  let p := naturalValue addOp zero one (s 253)
  let n := naturalValue addOp zero one (s 254)
  let neg := mulOp n minusOne
  let out := addOp p neg
  let s1 := Function.update s 246 (s 253)
  let s2 := Function.update s 247 (encode p)
  let s3 := Function.update s2 255 (encode p)
  let s4 := Function.update s 255 (encode p)
  let s5 := Function.update s4 246 (s 254)
  let s6 := Function.update s4 247 (encode n)
  let s7 := Function.update s4 247 (encode neg)
  let s8 := Function.update s7 255 (encode out)
  have hf1 : LowFrame base s1 := lowFrame_update hf 246 (by decide) _
  have hf4 : LowFrame base s4 := lowFrame_update hf 255 (by decide) _
  have hf5 : LowFrame base s5 := lowFrame_update hf4 246 (by decide) _
  have hf6 : LowFrame base s6 := lowFrame_update hf4 247 (by decide) _
  have hf7 : LowFrame base s7 := lowFrame_update hf4 247 (by decide) _
  have h1 : ExecutesIn (copy 253 246) (7*(s 253).length+5) s s1 := by
    simpa [s1, h246] using copy_run 253 246 s (by decide) (by decide) (by decide) hc.1
  have h2 : ExecutesIn (naturalCommand add) (naturalBudget (s 253).length Ka W) s1 s2 := by
    have h := naturalCommand_run base encode add addOp Ka W ha hw s1 zero one hf1
      (by simpa [Clean, s1] using hc) (by simp [s1, hz]) (by simp [s1, ho])
      (by simp [s1, h247]) (by simp [s1, h248])
    have he : Function.update (Function.update s1 246 []) 247
        (encode (naturalValue addOp zero one (s1 246))) = s2 := by
      simp [s1, s2, p, ← h246]
    rw [he] at h
    simpa only [s1, Function.update_self] using h
  have h3 : ExecutesIn (copy 247 255) (7*W+5) s2 s3 := by
    have h := copy_run 247 255 s2 (by decide) (by decide) (by decide) (by simp [s2, hc.1])
    simp only [s2, Function.update_self, Function.update_of_ne (show (255 : Fin 256) ≠ 247 by decide),
      h255, List.append_nil] at h
    exact h.mono (by have := hw p; omega)
  have h4 : ExecutesIn (clear 247) (2*W+3) s3 s4 := by
    have h := clear_run 247 s3
    have he : Function.update s3 247 [] = s4 := by
      funext i
      by_cases hi : i = 247 <;> simp [s3, s2, s4, Function.update_apply, hi, h247]
    rw [he] at h
    exact h.mono (by have := hw p; simp [s3, s2]; omega)
  have h5 : ExecutesIn (copy 254 246) (7*(s 254).length+5) s4 s5 := by
    have h := copy_run 254 246 s4 (by decide) (by decide) (by decide) (by simp [s4, hc.1])
    simpa [s5, s4, h246] using h
  have h6 : ExecutesIn (naturalCommand add) (naturalBudget (s 254).length Ka W) s5 s6 := by
    have h := naturalCommand_run base encode add addOp Ka W ha hw s5 zero one hf5
      (by simpa [Clean, s5, s4] using hc) (by simp [s5, s4, hz]) (by simp [s5, s4, ho])
      (by simp [s5, s4, h247]) (by simp [s5, s4, h248])
    have he : Function.update (Function.update s5 246 []) 247
        (encode (naturalValue addOp zero one (s5 246))) = s6 := by
      funext i
      by_cases hi : i = 246 <;> by_cases hj : i = 247 <;>
        simp [s5, s4, s6, n, Function.update_apply, hi, hj, h246]
    rw [he] at h
    simpa only [s5, Function.update_self] using h
  have h7 : ExecutesIn (callAt multiply 247 251 247) (Km+40*W+50) s6 s7 := by
    have h := callAt_run base encode multiply mulOp Km W hm hw s6 n minusOne
      247 251 247 (by unfold CRTLocalProgram.CachePort; decide) (by unfold CRTLocalProgram.CachePort; decide) (by unfold CRTLocalProgram.CachePort; decide) hf6
      (by simp [s6]) (by simp [s6, s4, hn])
      (by simp [s6, s4, hc.1]) (by simp [s6, s4, hc.2.1])
      (by simp [s6, s4, hc.2.2.1]) (by simp [s6, s4, hc.2.2.2.1])
      (by simp [s6, s4, hc.2.2.2.2]) (by simpa [s6] using hw n)
    simpa [s6, s7, neg] using h
  have h8 : ExecutesIn (callAt add 255 247 255) (Ka+40*W+50) s7 s8 :=
    callAt_run base encode add addOp Ka W ha hw s7 p neg
      255 247 255 (by unfold CRTLocalProgram.CachePort; decide) (by unfold CRTLocalProgram.CachePort; decide) (by unfold CRTLocalProgram.CachePort; decide) hf7
      (by simp [s7, s4]) (by simp [s7])
      (by simp [s7, s4, hc.1]) (by simp [s7, s4, hc.2.1])
      (by simp [s7, s4, hc.2.2.1]) (by simp [s7, s4, hc.2.2.2.1])
      (by simp [s7, s4, hc.2.2.2.2]) (by simpa [s7, s4] using hw p)
  have h9 : ExecutesIn (clear 247) (2*W+3) s8 (Function.update s 255 (encode out)) := by
    have h := clear_run 247 s8
    have he : Function.update s8 247 [] = Function.update s 255 (encode out) := by
      funext i
      by_cases hi : i = 247 <;> by_cases hj : i = 255 <;>
        simp [s8, s7, s4, hi, hj, h247]
    rw [he] at h
    exact h.mono (by have := hw neg; simp [s8, s7]; omega)
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq h9)))))))
  apply h.mono
  simp only [signedBudget, naturalBudget]
  ring_nf
  omega

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms

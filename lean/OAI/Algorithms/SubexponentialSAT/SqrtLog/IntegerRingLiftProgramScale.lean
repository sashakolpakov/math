import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgramSigned

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update callAt callAt_run)

/-- The source-row convention: negate the signed lift times cached inverse
denominator252. Both the denominator and minus-one251 are retained. -/
def scaledCommand (multiply add : Code) : Code :=
  .seq (signedCommand multiply add) (.seq (callAt multiply 255 252 255)
    (callAt multiply 255 251 255))

def scaledValue {C : Type*} (mul add : C → C → C) (zero one minusOne invDenom : C)
    (positive negative : List Bool) : C :=
  mul (mul (signedValue mul add zero one minusOne positive negative) invDenom) minusOne

def scaledBudget (bits Km Ka W : ℕ) : ℕ := signedBudget bits Km Ka W + 2*(Km+40*W+50)

theorem scaledValue_decode {C A : Type*} [CommRing A] (decode : C → A)
    (mul add : C → C → C)
    (hm : ∀ x y, decode (mul x y) = decode x * decode y)
    (ha : ∀ x y, decode (add x y) = decode x + decode y)
    (zero one minusOne invDenom : C) (hz : decode zero = 0) (ho : decode one = 1)
    (hn : decode minusOne = -1) (positive negative : List Bool) :
    decode (scaledValue mul add zero one minusOne invDenom positive negative) =
      -(decode invDenom) * (((BinaryArithmetic.toNat positive : ℤ) -
        (BinaryArithmetic.toNat negative : ℤ) : ℤ) : A) := by
  rw [scaledValue, hm, hm, signedValue_decode decode mul add hm ha zero one minusOne hz ho hn,
    hn]
  ring

theorem scaledCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka) (hw : ∀ a, (encode a).length ≤ W)
    (s : Store) (zero one minusOne invDenom : C) (hf : LowFrame base s) (hc : Clean s)
    (hz : s 249 = encode zero) (ho : s 250 = encode one) (hn : s 251 = encode minusOne)
    (hinv : s 252 = encode invDenom)
    (h246 : s 246 = []) (h247 : s 247 = []) (h248 : s 248 = []) (h255 : s 255 = []) :
    ExecutesIn (scaledCommand multiply add)
      (scaledBudget ((s 253).length + (s 254).length) Km Ka W) s
      (Function.update s 255 (encode (scaledValue mulOp addOp zero one minusOne invDenom
        (s 253) (s 254)))) := by
  let x := signedValue mulOp addOp zero one minusOne (s 253) (s 254)
  let y := mulOp x invDenom
  let z := mulOp y minusOne
  let s1 := Function.update s 255 (encode x)
  let s2 := Function.update s 255 (encode y)
  have h1 := signedCommand_run base encode multiply add mulOp addOp Km Ka W hm ha hw
    s zero one minusOne hf hc hz ho hn h246 h247 h248 h255
  have hf1 : LowFrame base s1 := lowFrame_update hf 255 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf 255 (by decide) _
  have h2 : ExecutesIn (callAt multiply 255 252 255) (Km+40*W+50) s1 s2 := by
    have h := callAt_run base encode multiply mulOp Km W hm hw s1 x invDenom
      255 252 255 (by unfold CRTLocalProgram.CachePort; decide) (by unfold CRTLocalProgram.CachePort; decide) (by unfold CRTLocalProgram.CachePort; decide) hf1 (by simp [s1])
      (by simp [s1, hinv]) (by simp [s1, hc.1]) (by simp [s1, hc.2.1])
      (by simp [s1, hc.2.2.1]) (by simp [s1, hc.2.2.2.1])
      (by simp [s1, hc.2.2.2.2]) (by simpa [s1] using hw x)
    simpa [s1, s2, y] using h
  have h3 : ExecutesIn (callAt multiply 255 251 255) (Km+40*W+50) s2
      (Function.update s 255 (encode z)) := by
    have h := callAt_run base encode multiply mulOp Km W hm hw s2 y minusOne
      255 251 255 (by unfold CRTLocalProgram.CachePort; decide) (by unfold CRTLocalProgram.CachePort; decide) (by unfold CRTLocalProgram.CachePort; decide) hf2 (by simp [s2])
      (by simp [s2, hn]) (by simp [s2, hc.1]) (by simp [s2, hc.2.1])
      (by simp [s2, hc.2.2.1]) (by simp [s2, hc.2.2.2.1])
      (by simp [s2, hc.2.2.2.2]) (by simpa [s2] using hw y)
    simpa [s2, z] using h
  exact (h1.seq (h2.seq h3)).mono (by unfold scaledBudget; omega)

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms

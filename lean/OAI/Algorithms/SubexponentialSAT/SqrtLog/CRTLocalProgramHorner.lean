import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramLoops

namespace OAI.Algorithms

/-! Native fixed-control Horner iteration, shared by scalar nilpotent repair
and the independently truncated local polynomial inverse. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def hornerStep (multiply add : Code) : Code :=
  .seq (binaryStep multiply)
    (.seq (replace 220 241) (.seq (binaryStep add) (replace 222 241)))

def hornerCommand (multiply add : Code) : Code := nativeRepeat (hornerStep multiply add)

def hornerValue {C : Type*} (mul add : C → C → C) (z one a : C) : C :=
  add (mul a z) one

theorem hornerStep_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (a z one : C) (hf : LowFrame base s)
    (hacc : s 240 = encode a) (hfactor : s 241 = encode z)
    (hone : s 220 = encode one) (hz : s 222 = encode z)
    (h120 : s 120 = []) (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn (hornerStep multiply add) (Km + Ka + 34 * W + 34) s
      (Function.update s 240 (encode (hornerValue mulOp addOp z one a))) := by
  let p := mulOp a z
  let v := addOp p one
  let s1 := Function.update s 240 (encode p)
  let s2 := Function.update s1 241 (encode one)
  let s3 := Function.update s2 240 (encode v)
  have hf1 : LowFrame base s1 := lowFrame_update hf 240 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf1 241 (by decide) _
  have h1 : ExecutesIn (binaryStep multiply) (Km + 8 * W + 9) s s1 :=
    binaryStep_run base encode multiply mulOp Km W hm hwidth s a z hf
      hacc hfactor h244 h245
  have h2 : ExecutesIn (replace 220 241) (9 * W + 8) s1 s2 := by
    have h := replace_run s1 220 241 (by decide) (by decide) (by decide)
      (by simp [s1, h120])
    have he : Function.update s1 241 (s1 220) = s2 := by simp [s2, s1, hone]
    rw [he] at h
    apply h.mono
    simp only [s1, Function.update_of_ne (show (241 : Fin 256) ≠ 240 by decide),
      Function.update_of_ne (show (220 : Fin 256) ≠ 240 by decide), hfactor, hone]
    have hwz := hwidth z
    have hwo := hwidth one
    omega
  have h3 : ExecutesIn (binaryStep add) (Ka + 8 * W + 9) s2 s3 :=
    binaryStep_run base encode add addOp Ka W ha hwidth s2 p one hf2
      (by simp [s2, s1]) (by simp [s2])
      (by simp [s2, s1, h244]) (by simp [s2, s1, h245])
  have h4 : ExecutesIn (replace 222 241) (9 * W + 8) s3
      (Function.update s 240 (encode v)) := by
    have h := replace_run s3 222 241 (by decide) (by decide) (by decide)
      (by simp [s3, s2, s1, h120])
    have he : Function.update s3 241 (s3 222) = Function.update s 240 (encode v) := by
      funext i
      by_cases hi : i = 241 <;> by_cases ha : i = 240 <;>
        simp [s3, s2, s1, hi, ha, hz, hfactor]
    rw [he] at h
    apply h.mono
    simp [s3, s2, s1, hz]
    have hwz := hwidth z
    have hwo := hwidth one
    omega
  have h := h1.seq (h2.seq (h3.seq h4))
  convert h using 1 <;> first | omega | rfl

theorem hornerCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (z one seed : C) (hfactor : base 241 = encode z)
    (hone : base 220 = encode one) (hz : base 222 = encode z)
    (h120 : base 120 = []) (h244 : base 244 = []) (h245 : base 245 = [])
    (counter : List Bool) :
    ExecutesIn (hornerCommand multiply add)
      (counter.length * (Km + Ka + 34 * W + 36) + 2)
      (loopReady base encode seed counter)
      (loopReady base encode ((hornerValue mulOp addOp z one)^[counter.length] seed) []) := by
  have hstep (a : C) (count : List Bool) :
      ExecutesIn (hornerStep multiply add) (Km + Ka + 34 * W + 34)
        (loopReady base encode a count)
        (loopReady base encode (hornerValue mulOp addOp z one a) count) := by
    have h := hornerStep_run base encode multiply add mulOp addOp Km Ka W hm ha hwidth
      (loopReady base encode a count) a z one (lowFrame_loopReady base encode a count)
      (by simp [loopReady, SubexpPolynomialIterationControl.ready])
      (by simpa [loopReady, SubexpPolynomialIterationControl.ready] using hfactor)
      (by simpa [loopReady, SubexpPolynomialIterationControl.ready] using hone)
      (by simpa [loopReady, SubexpPolynomialIterationControl.ready] using hz)
      (by simpa [loopReady, SubexpPolynomialIterationControl.ready] using h120)
      (by simpa [loopReady, SubexpPolynomialIterationControl.ready] using h244)
      (by simpa [loopReady, SubexpPolynomialIterationControl.ready] using h245)
    convert h using 1
    funext i
    by_cases hi : i = 240 <;> by_cases hc : i = 246 <;>
      simp [loopReady, SubexpPolynomialIterationControl.ready, hi, hc]
  simpa only [hornerCommand, nativeRepeat, loopReady,
      show Km + Ka + 34 * W + 34 + 2 = Km + Ka + 34 * W + 36 by omega] using
    SubexpPolynomialIterationControl.repeat_run base encode (hornerStep multiply add)
      (hornerValue mulOp addOp z one) (Km + Ka + 34 * W + 34) hstep counter seed

theorem hornerValue_decode {C A : Type*} [CommRing A] (decode : C → A)
    (mulOp addOp : C → C → C)
    (hm : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (ha : ∀ a b, decode (addOp a b) = decode a + decode b)
    (z one seed : C) (hone : decode one = 1) (hseed : decode seed = 0) (n : ℕ) :
    decode ((hornerValue mulOp addOp z one)^[n] seed) =
      ∑ i ∈ Finset.range n, decode z ^ i := by
  induction n with
  | zero => simpa using hseed
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      simp only [hornerValue, ha, hm, hone, ih]
      simpa only [mul_comm] using (@geom_sum_succ A _ (decode z) n).symm

theorem hornerCommand_state {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (z one seed : C) (hf : LowFrame base s)
    (hseed : s 240 = encode seed) (hfactor : s 241 = encode z)
    (hone : s 220 = encode one) (hz : s 222 = encode z)
    (h120 : s 120 = []) (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn (hornerCommand multiply add)
      ((s 246).length * (Km + Ka + 34 * W + 36) + 2) s
      (Function.update (Function.update s 240
        (encode ((hornerValue mulOp addOp z one)^[(s 246).length] seed))) 246 []) := by
  have h := hornerCommand_run s encode multiply add mulOp addOp Km Ka W
    (serviceSpec_frame hm hf) (serviceSpec_frame ha hf) hwidth z one seed
    hfactor hone hz h120 h244 h245 (s 246)
  have hi : loopReady s encode seed (s 246) = s := by
    simp [loopReady, SubexpPolynomialIterationControl.ready, ← hseed]
  rw [hi] at h
  exact h

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms

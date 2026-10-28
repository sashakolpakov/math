import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialIterationControl
import OAI.Algorithms.SubexponentialSAT.SubexpResidueInverse

namespace OAI.Algorithms

/-! Fixed native loops used by independent-precision local Hermite CRT.

The arithmetic argument is a finite `Cmd`, never a semantic instruction.
`ServiceSpec` is the exact trace contract discharged by the native represented
ring/array callbacks. All iteration counts remain on runtime stack 246.
-/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

abbrev Store := Fin 256 → List Bool

/-- The shared arithmetic workspace is below the persistent CRT ports. -/
def LowFrame (base s : Store) : Prop := ∀ i : Fin 256, i.val < 205 → s i = base i

theorem lowFrame_refl (s : Store) : LowFrame s s := fun _ _ => rfl

theorem lowFrame_trans {a b c : Store} (hab : LowFrame a b) (hbc : LowFrame b c) :
    LowFrame a c := fun i hi => (hbc i hi).trans (hab i hi)

theorem lowFrame_update {base s : Store} (h : LowFrame base s)
    (i : Fin 256) (hi : 205 ≤ i.val) (v : List Bool) :
    LowFrame base (Function.update s i v) := by
  intro j hj
  have hji : j ≠ i := by intro he; subst j; omega
  simpa [hji] using h j hj

/-- Arithmetic consumes neither input. Its sole changed stack is output 244. -/
def ServiceSpec {C : Type*} (base : Store) (encode : C → List Bool)
    (code : Code) (op : C → C → C) (K : ℕ) : Prop :=
  ∀ (s : Store) (a b : C), LowFrame base s →
    s 240 = encode a → s 241 = encode b → s 244 = [] → s 245 = [] →
    ExecutesIn code K s (Function.update s 244 (encode (op a b)))

theorem serviceSpec_frame {C : Type*} {base next : Store} {encode : C → List Bool}
    {code : Code} {op : C → C → C} {K : ℕ}
    (h : ServiceSpec base encode code op K) (hn : LowFrame base next) :
    ServiceSpec next encode code op K := by
  intro s a b hs
  exact h s a b (lowFrame_trans hn hs)

def binaryStep (code : Code) : Code := SubexpPolynomialIterationControl.step code
def nativeRepeat (code : Code) : Code := SubexpPolynomialIterationControl.repeatLoop code

theorem binaryStep_run {C : Type*} (base : Store) (encode : C → List Bool)
    (code : Code) (op : C → C → C) (K W : ℕ)
    (hspec : ServiceSpec base encode code op K)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (a b : C) (hf : LowFrame base s)
    (ha : s 240 = encode a) (hb : s 241 = encode b)
    (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn (binaryStep code) (K + 8 * W + 9) s
      (Function.update s 240 (encode (op a b))) := by
  have h := SubexpPolynomialIterationControl.step_run code K s
    (encode (op a b)) h244 h245 (hspec s a b hf ha hb h244 h245)
  apply h.mono
  rw [ha]
  have h1 := hwidth a
  have h2 := hwidth (op a b)
  omega

/-- Replace a high persistent port by a preserving copy from another port. -/
def replace (src dst : Fin 256) : Code := .seq (clear dst) (copy src dst)

theorem replace_run (s : Store) (src dst : Fin 256)
    (hsd : src ≠ dst) (hs : src ≠ 120) (hd : dst ≠ 120)
    (h120 : s 120 = []) :
    ExecutesIn (replace src dst)
      (2 * (s dst).length + 7 * (s src).length + 8)
      s (Function.update s dst (s src)) := by
  have h1 := clear_run dst s
  have h2 := copy_run src dst (Function.update s dst []) hsd hs (Ne.symm hd)
    (by simpa [Ne.symm hd] using h120)
  have he : Function.update (Function.update s dst []) dst
      ((Function.update s dst []) src ++ (Function.update s dst []) dst) =
      Function.update s dst (s src) := by simp [hsd]
  rw [he] at h2
  have h := h1.seq h2
  convert h using 1
  · rfl
  · simp [hsd]
    ring

theorem replace_bounded (s : Store) (src dst : Fin 256) (W : ℕ)
    (hsd : src ≠ dst) (hs : src ≠ 120) (hd : dst ≠ 120)
    (h120 : s 120 = []) (hsrc : (s src).length ≤ W) (hdst : (s dst).length ≤ W) :
    ExecutesIn (replace src dst) (9 * W + 8) s (Function.update s dst (s src)) :=
  (replace_run s src dst hsd hs hd h120).mono (by omega)

abbrev loopReady {C : Type*} (base : Store) (encode : C → List Bool)
    (a : C) (counter : List Bool) : Store :=
  SubexpPolynomialIterationControl.ready base encode a counter

theorem lowFrame_loopReady {C : Type*} (base : Store) (encode : C → List Bool)
    (a : C) (counter : List Bool) : LowFrame base (loopReady base encode a counter) :=
  lowFrame_update (lowFrame_update (lowFrame_refl base) 240 (by decide) _) 246 (by decide) _

theorem binary_repeat_run {C : Type*} (base : Store) (encode : C → List Bool)
    (code : Code) (op : C → C → C) (K W : ℕ)
    (hspec : ServiceSpec base encode code op K)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (factor seed : C) (hfactor : base 241 = encode factor)
    (h244 : base 244 = []) (h245 : base 245 = []) (counter : List Bool) :
    ExecutesIn (nativeRepeat (binaryStep code))
      (counter.length * (K + 8 * W + 11) + 2)
      (loopReady base encode seed counter)
      (loopReady base encode ((fun a => op a factor)^[counter.length] seed) []) := by
  have hstep (a : C) (count : List Bool) :
      ExecutesIn (binaryStep code) (K + 8 * W + 9)
        (loopReady base encode a count)
        (loopReady base encode (op a factor) count) := by
    have h := binaryStep_run base encode code op K W hspec hwidth
      (loopReady base encode a count) a factor
      (lowFrame_loopReady base encode a count)
      (by simp [loopReady, SubexpPolynomialIterationControl.ready])
      (by simpa [loopReady, SubexpPolynomialIterationControl.ready] using hfactor)
      (by simpa [loopReady, SubexpPolynomialIterationControl.ready] using h244)
      (by simpa [loopReady, SubexpPolynomialIterationControl.ready] using h245)
    convert h using 1
    funext i
    by_cases hi : i = 240 <;> by_cases hc : i = 246 <;>
      simp [loopReady, SubexpPolynomialIterationControl.ready, hi, hc]
  simpa only [nativeRepeat, loopReady,
    show K + 8 * W + 9 + 2 = K + 8 * W + 11 by omega] using
    SubexpPolynomialIterationControl.repeat_run base encode (binaryStep code)
      (fun a => op a factor) (K + 8 * W + 9) hstep counter seed

theorem iterate_mul_decode {C A : Type*} [Monoid A] (encode : C → A)
    (mul : C → C → C) (h : ∀ a b, encode (mul a b) = encode a * encode b)
    (a seed : C) (n : ℕ) :
    encode ((fun x => mul x a)^[n] seed) = encode seed * encode a ^ n := by
  induction n generalizing seed with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, h, pow_succ']
      simp only [mul_assoc]

theorem binary_repeat_state {C : Type*} (base : Store) (encode : C → List Bool)
    (code : Code) (op : C → C → C) (K W : ℕ)
    (hspec : ServiceSpec base encode code op K)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (factor seed : C) (hf : LowFrame base s)
    (hseed : s 240 = encode seed) (hfactor : s 241 = encode factor)
    (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn (nativeRepeat (binaryStep code))
      ((s 246).length * (K + 8 * W + 11) + 2) s
      (Function.update (Function.update s 240
        (encode ((fun a => op a factor)^[(s 246).length] seed))) 246 []) := by
  have h := binary_repeat_run s encode code op K W (serviceSpec_frame hspec hf)
    hwidth factor seed hfactor h244 h245 (s 246)
  have hi : loopReady s encode seed (s 246) = s := by
    simp [loopReady, SubexpPolynomialIterationControl.ready, ← hseed]
  rw [hi] at h
  exact h

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramRing
import OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl

namespace OAI.Algorithms

/-! Native scalar cofactor construction for the Hermite value at zero. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (LowFrame ServiceSpec binaryStep nativeRepeat replace loopReady)

theorem reframe_service {C : Type*} {base s : Store} (hf : LowFrame base s)
    (encode : C → List Bool) (code : Code) (op : C → C → C) (K : ℕ)
    (h : ServiceSpec base encode code op K) : ServiceSpec s encode code op K := by
  intro t a b ht ha hb ho htmp
  apply h t a b _ ha hb ho htmp
  intro i hi
  exact (ht i hi).trans (hf i hi)

/-- Repetition can start in any framed caller state. Its counter is consumed. -/
theorem repeat_at_state {C : Type*} (base : Store) (encode : C → List Bool)
    (code : Code) (op : C → C → C) (K W : ℕ)
    (hspec : ServiceSpec base encode code op K) (hw : ∀ a, (encode a).length ≤ W)
    (s : Store) (hf : LowFrame base s) (factor seed : C)
    (h240 : s 240 = encode seed) (h241 : s 241 = encode factor)
    (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = []) (counter : List Bool) :
    ExecutesIn (nativeRepeat (binaryStep code))
      (counter.length * (K + 8 * W + 11) + 2)
      (Function.update s 246 counter)
      (Function.update s 240 (encode ((fun a => op a factor)^[counter.length] seed))) := by
  have h := CRTLocalProgram.binary_repeat_run s encode code op K W
    (reframe_service hf encode code op K hspec) hw factor seed h241 h244 h245 counter
  have hin : loopReady s encode seed counter = Function.update s 246 counter := by
    simp [loopReady, SubexpPolynomialIterationControl.ready, ← h240]
  have hout : loopReady s encode ((fun a => op a factor)^[counter.length] seed) [] =
      Function.update s 240 (encode ((fun a => op a factor)^[counter.length] seed)) := by
    funext i
    by_cases hi : i = 246 <;> by_cases hj : i = 240 <;>
      simp [loopReady, SubexpPolynomialIterationControl.ready, hi, hj, h246]
  simpa only [hin, hout] using h

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

/-- Save the accumulator, form minus-node by actual multiplication, then
multiply the saved accumulator by that value J times. -/
def includeNode (multiply : Code) : Code :=
  replace 240 223 ;; replace 218 240 ;; replace 211 241 ;; binaryStep multiply ;;
  replace 240 219 ;; replace 223 240 ;; replace 219 241 ;; clear 223 ;;
  copy 243 246 ;; nativeRepeat (binaryStep multiply) ;; clear 241

def includeBudget (K W J : ℕ) : ℕ := (J + 1) * (K + 8 * W + 11) + 63 * W + 7 * J + 70

def includeValue {C : Type*} (mul : C → C → C) (minusOne : C) (J : ℕ) (a c : C) : C :=
  (fun x => mul x (mul c minusOne))^[J] a


theorem replace_bound (s : Store) (src dst : Fin 256) (W : ℕ)
    (hsd : src ≠ dst) (hs : src ≠ 120) (hd : dst ≠ 120)
    (ht : s 120 = []) (hsrc : (s src).length ≤ W) (hdst : (s dst).length ≤ W) :
    ExecutesIn (replace src dst) (9 * W + 8) s (Function.update s dst (s src)) :=
  (CRTLocalProgram.replace_run s src dst hsd hs hd ht).mono (by omega)

theorem includeNode_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply : Code) (mul : C → C → C) (minusOne : C) (K W J : ℕ)
    (hspec : ServiceSpec base encode multiply mul K)
    (hw : ∀ a, (encode a).length ≤ W)
    (s : Store) (a c : C) (hf : LowFrame base s)
    (ha : s 240 = encode a) (hc : s 218 = encode c) (hm : s 211 = encode minusOne)
    (hj : s 243 = List.replicate J true)
    (h120 : s 120 = []) (h219 : s 219 = []) (h223 : s 223 = [])
    (h241 : s 241 = []) (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = []) :
    ExecutesIn (includeNode multiply) (includeBudget K W J) s
      (Function.update (Function.update s 240 (encode (includeValue mul minusOne J a c)))
        219 (encode (mul c minusOne))) := by
  let neg := mul c minusOne
  let s1 := Function.update s 223 (encode a)
  let s2 := Function.update s1 240 (encode c)
  let s3 := Function.update s2 241 (encode minusOne)
  let s4 := Function.update s3 240 (encode neg)
  let s5 := Function.update s4 219 (encode neg)
  let s6 := Function.update s5 240 (encode a)
  let s7 := Function.update s6 241 (encode neg)
  let s8 := Function.update (Function.update s 219 (encode neg)) 241 (encode neg)
  have h1 : ExecutesIn (replace 240 223) (9 * W + 8) s s1 := by
    simpa [s1, ha] using replace_bound s 240 223 W (by decide) (by decide) (by decide)
      h120 (by simpa [ha] using hw a) (by simp [h223])
  have h2 : ExecutesIn (replace 218 240) (9 * W + 8) s1 s2 := by
    simpa [s2, s1, hc] using replace_bound s1 218 240 W (by decide) (by decide) (by decide)
      (by simp [s1, h120]) (by simpa [s1, hc] using hw c) (by simpa [s1, ha] using hw a)
  have h3 : ExecutesIn (replace 211 241) (9 * W + 8) s2 s3 := by
    simpa [s3, s2, s1, hm] using replace_bound s2 211 241 W (by decide) (by decide) (by decide)
      (by simp [s2, s1, h120]) (by simpa [s2, s1, hm] using hw minusOne)
      (by simp [s2, s1, h241])
  have hf3 : LowFrame base s3 := by
    intro i hi
    have h1 : i ≠ 223 := by intro h; subst i; omega
    have h2 : i ≠ 240 := by intro h; subst i; omega
    have h3 : i ≠ 241 := by intro h; subst i; omega
    simpa [s3, s2, s1, h1, h2, h3] using hf i hi
  have h4 : ExecutesIn (binaryStep multiply) (K + 8 * W + 9) s3 s4 := by
    apply CRTLocalProgram.binaryStep_run base encode multiply mul K W hspec hw s3 c minusOne hf3
    all_goals simp [ s3, s2, s1, h244, h245]
  have h5 : ExecutesIn (replace 240 219) (9 * W + 8) s4 s5 := by
    simpa [s5, s4] using replace_bound s4 240 219 W (by decide) (by decide) (by decide)
      (by simp [s4, s3, s2, s1, h120]) (by simp [s4]; exact hw neg)
      (by simp [s4, s3, s2, s1, h219])
  have h6 : ExecutesIn (replace 223 240) (9 * W + 8) s5 s6 := by
    simpa [s6, s5, s4, s3, s2, s1] using
      replace_bound s5 223 240 W (by decide) (by decide) (by decide)
        (by simp [s5, s4, s3, s2, s1, h120])
        (by simpa [s5, s4, s3, s2, s1] using hw a)
        (by simpa [s5, s4] using hw neg)
  have h7 : ExecutesIn (replace 219 241) (9 * W + 8) s6 s7 := by
    simpa [s7, s6, s5] using replace_bound s6 219 241 W (by decide) (by decide) (by decide)
      (by simp [s6, s5, s4, s3, s2, s1, h120])
      (by simpa [s6, s5] using hw neg)
      (by simpa [s6, s5, s4, s3] using hw minusOne)
  have he8 : Function.update s7 223 [] = s8 := by
    funext i
    by_cases h1 : i = 223 <;> by_cases h2 : i = 240 <;>
      by_cases h3 : i = 241 <;> by_cases h4 : i = 219 <;>
      simp [s8, s7, s6, s5, s4, s3, s2, s1,
        h1, h2, h3, h4, h223, ha]
  have h8 : ExecutesIn (clear 223) (2 * W + 3) s7 s8 := by
    have h := clear_run 223 s7
    rw [he8] at h
    apply h.mono
    simpa [s7, s6, s5, s4, s3, s2, s1] using Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hw a)) 3
  have h9 : ExecutesIn (copy 243 246) (7 * J + 5) s8
      (Function.update s8 246 (List.replicate J true)) := by
    simpa [s8, hj, h246] using copy_run 243 246 s8 (by decide) (by decide) (by decide)
      (by simp [s8, h120])
  have hf8 : LowFrame base s8 := by
    intro i hi
    have h1 : i ≠ 219 := by intro h; subst i; omega
    have h2 : i ≠ 241 := by intro h; subst i; omega
    simpa [s8, h1, h2] using hf i hi
  have h10 : ExecutesIn (nativeRepeat (binaryStep multiply))
      (J * (K + 8 * W + 11) + 2)
      (Function.update s8 246 (List.replicate J true))
      (Function.update s8 240 (encode (includeValue mul minusOne J a c))) := by
    simpa only [List.length_replicate, includeValue, neg] using repeat_at_state base encode multiply mul K W hspec hw
      s8 hf8 neg a (by simp [s8, ha]) (by simp [s8])
      (by simp [s8, h244]) (by simp [s8, h245]) (by simp [s8, h246]) (List.replicate J true)
  have h11 : ExecutesIn (clear 241) (2 * W + 3)
      (Function.update s8 240 (encode (includeValue mul minusOne J a c)))
      (Function.update (Function.update s 240 (encode (includeValue mul minusOne J a c)))
        219 (encode neg)) := by
    have h := clear_run 241 (Function.update s8 240 (encode (includeValue mul minusOne J a c)))
    have he : Function.update (Function.update s8 240 (encode (includeValue mul minusOne J a c))) 241 [] =
        Function.update (Function.update s 240 (encode (includeValue mul minusOne J a c))) 219 (encode neg) := by
      funext i
      by_cases h1 : i = 219 <;> by_cases h2 : i = 241 <;> by_cases h3 : i = 240 <;>
        simp [s8, h1, h2, h3, h241]
    rw [he] at h
    apply h.mono
    simpa [s8] using Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hw neg)) 3
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq h11)))))))))
  apply h.mono
  unfold includeBudget
  nlinarith

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

end OAI.Algorithms

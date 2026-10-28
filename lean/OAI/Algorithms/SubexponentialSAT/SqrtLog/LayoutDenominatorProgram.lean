import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramLoops

namespace OAI.Algorithms

/-! Fixed native exponentiation for the common layout denominator. The unary
row parameter is retained at239; the represented half starts at255 and one at250.
The output252 is computed by exactly `R-1` native multiplications. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update nativeRepeat binaryStep binary_repeat_state)

def powerCommand (multiply : Code) : Code :=
  .seq (copy 255 241) (.seq (copy 250 240) (.seq (copy 239 246)
    (.seq (popToken 246) (.seq (nativeRepeat (binaryStep multiply))
      (.seq (copy 240 252) (.seq (clear 240) (.seq (clear 241) (clear 255))))))))

def powerValue {C : Type*} (mul : C → C → C) (half one : C) (R : ℕ) : C :=
  (fun x => mul x half)^[R-1] one

def powerBudget (R K W : ℕ) : ℕ :=
  (R-1)*(K+8*W+11)+7*R+27*W+32

theorem popToken_tail_run (s : Store) (i : Fin 256) :
    ExecutesIn (popToken i) 1 s (Function.update s i (s i).tail) := by
  intro regs
  refine ⟨1, readRegs regs 0 1 (s i).head?, le_rfl, ?_⟩
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop i 0 1)
    (⟨regs,s⟩ : Data)
  simpa [popToken, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr]
    using Eval.base h

theorem powerCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply : Code) (mul : C → C → C) (K W : ℕ)
    (hm : ServiceSpec base encode multiply mul K) (hw : ∀ x, (encode x).length ≤ W)
    (s : Store) (half one : C) (hf : LowFrame base s)
    (hhalf : s 255 = encode half) (hone : s 250 = encode one)
    (h120 : s 120 = []) (h240 : s 240 = []) (h241 : s 241 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = [])
    (h252 : s 252 = []) :
    ExecutesIn (powerCommand multiply) (powerBudget (s 239).length K W) s
      (Function.update (Function.update s 255 []) 252
        (encode (powerValue mul half one (s 239).length))) := by
  let out := powerValue mul half one (s 239).length
  let s1 := Function.update s 241 (encode half)
  let s2 := Function.update s1 240 (encode one)
  let s3 := Function.update s2 246 (s 239)
  let s4 := Function.update s2 246 (s 239).tail
  let s5 := Function.update s1 240 (encode out)
  let s6 := Function.update s5 252 (encode out)
  let s7 := Function.update s1 252 (encode out)
  let s8 := Function.update s 252 (encode out)
  have h1 : ExecutesIn (copy 255 241) (7*W+5) s s1 := by
    have h := copy_run 255 241 s (by decide) (by decide) (by decide) h120
    simp only [hhalf,h241,List.append_nil] at h
    exact h.mono (by have := hw half; omega)
  have h2 : ExecutesIn (copy 250 240) (7*W+5) s1 s2 := by
    have h := copy_run 250 240 s1 (by decide) (by decide) (by decide)
      (by simp [s1,h120])
    simpa [s2,s1,hone,h240] using h.mono (by simpa [s1,hone] using (Nat.add_le_add_right (Nat.mul_le_mul_left 7 (hw one)) 5))
  have h3 : ExecutesIn (copy 239 246) (7*(s 239).length+5) s2 s3 := by
    simpa [s3,s2,s1,h246] using copy_run 239 246 s2
      (by decide) (by decide) (by decide) (by simp [s2,s1,h120])
  have h4 : ExecutesIn (popToken 246) 1 s3 s4 := by
    simpa [s3,s4] using popToken_tail_run s3 246
  have hf4 : LowFrame base s4 := lowFrame_update
    (lowFrame_update (lowFrame_update hf 241 (by decide) _) 240 (by decide) _)
    246 (by decide) _
  have h5 : ExecutesIn (nativeRepeat (binaryStep multiply))
      (((s 239).length-1)*(K+8*W+11)+2) s4 s5 := by
    have h := binary_repeat_state base encode multiply mul K W hm hw s4 half one hf4
      (by simp [s4,s2,s1]) (by simp [s4,s2,s1])
      (by simp [s4,s2,s1,h244]) (by simp [s4,s2,s1,h245])
    have he : Function.update (Function.update s4 240
        (encode ((fun a => mul a half)^[(s4 246).length] one))) 246 [] = s5 := by
      funext i
      by_cases hi : i=240 <;> by_cases hj : i=246 <;>
        simp [s5,s4,s2,s1,out,powerValue,Function.update_apply,hi,hj,h246]
    rw [he] at h
    simpa only [s4,Function.update_self,List.length_tail] using h
  have h6 : ExecutesIn (copy 240 252) (7*W+5) s5 s6 := by
    have h := copy_run 240 252 s5 (by decide) (by decide) (by decide)
      (by simp [s5,s1,h120])
    simpa [s6,s5,s1,h252] using h.mono (by simpa [s5] using (Nat.add_le_add_right (Nat.mul_le_mul_left 7 (hw out)) 5))
  have h7 : ExecutesIn (clear 240) (2*W+3) s6 s7 := by
    have h := clear_run 240 s6
    have he : Function.update s6 240 [] = s7 := by
      funext i
      by_cases hi : i=240 <;> simp [s6,s5,s7,s1,Function.update_apply,hi,h240]
    rw [he] at h
    exact h.mono (by simpa [s6,s5] using (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hw out)) 3))
  have h8 : ExecutesIn (clear 241) (2*W+3) s7 s8 := by
    have h := clear_run 241 s7
    have he : Function.update s7 241 [] = s8 := by
      funext i
      by_cases hi : i=241 <;> simp [s7,s8,s1,Function.update_apply,hi,h241]
    rw [he] at h
    exact h.mono (by simpa [s7,s1] using (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hw half)) 3))
  have h9 : ExecutesIn (clear 255) (2*W+3) s8
      (Function.update (Function.update s 255 []) 252 (encode out)) := by
    have h := clear_run 255 s8
    have he : Function.update s8 255 [] =
        Function.update (Function.update s 255 []) 252 (encode out) := by
      funext i
      by_cases hi : i=255 <;> simp [s8,Function.update_apply,hi]
    rw [he] at h
    exact h.mono (by simpa [s8,hhalf] using (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hw half)) 3))
  exact (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq h9)))))))).mono
    (by unfold powerBudget; omega)

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgram

end OAI.Algorithms

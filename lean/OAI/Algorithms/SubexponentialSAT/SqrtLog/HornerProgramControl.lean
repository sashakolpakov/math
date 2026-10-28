import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramLoops
import OAI.Algorithms.SubexponentialSAT.SubexpHornerControl
import OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm

namespace OAI.Algorithms

/-! Fixed native streaming Horner control for arbitrary-width coefficient
representations. Arithmetic callbacks are finite commands with exact framed
traces. No loop bound or ring dimension occurs in the control table. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update binaryStep binaryStep_run)

/-- Read one reversed coefficient cell from the reversed polynomial stream. -/
def takeCoefficient : Code :=
  .seq (takeWord 250 251 252 246 241 0 1)
    (.call (StackRoutines.reverseProgram 241 251 252 (0 : Fin 16) 1))

theorem takeCoefficient_run (s : Store) (bits rest : List Bool)
    (hs : s 246 = bits.reverse ++ rest) (hw : (s 250).length = bits.length)
    (h241 : s 241 = []) (h251 : s 251 = []) (h252 : s 252 = []) :
    ExecutesIn takeCoefficient (23 * bits.length + 18) s
      (Function.update (Function.update s 246 rest) 241 bits) := by
  intro regs
  let d : Data := ⟨regs, s⟩
  have h1 := takeWord_eval d 250 251 252 246 241 0 1
    (by decide) (by decide) bits.reverse rest hs h251 h252 (by simpa using hw)
  let mid := afterTake d 246 241 0 1 bits.reverse rest
  have h2 := reverse_eval mid 241 251 252 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simp [mid, afterTake, d, h251]) (by simp [mid, afterTake, d, h252])
  have he : afterReverse mid 241 0 1 =
      (⟨readRegs regs 0 1 none,
        Function.update (Function.update s 246 rest) 241 bits⟩ : Data) := by
    apply state_ext
    · simp [afterReverse, mid, afterTake, d, StackRoutines.readRegs_reset]
    · simp [afterReverse, mid, afterTake, d, StackRoutines.reverseStacks, h241]
  rw [he] at h2
  have h := h1.seq h2
  refine ⟨14 * bits.reverse.length + 11 + (9 * (mid.stacks 241).length + 7),
    readRegs regs 0 1 none, ?_, ?_⟩
  · simp [mid, afterTake, d, h241]
    omega
  · simpa only [takeCoefficient] using h

/-- 240 accumulator; 246 stream; 247 point; 248 counter; 250 width.
241,244,245,251,252 are restored empty; all other stacks are framed. -/
def iteration (multiply add : Code) : Code :=
  .seq (copy 247 241) (.seq (binaryStep multiply)
    (.seq (clear 241) (.seq takeCoefficient (.seq (binaryStep add) (clear 241)))))

def stepValue {C : Type*} (mulOp addOp : C → C → C) (x a c : C) : C :=
  addOp (mulOp a x) c

theorem iteration_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length = W)
    (s : Store) (a x c : C) (rest : List Bool) (hf : LowFrame base s)
    (hacc : s 240 = encode a) (hx : s 247 = encode x)
    (hs : s 246 = (encode c).reverse ++ rest) (hw : (s 250).length = W)
    (h120 : s 120 = []) (h241 : s 241 = []) (h244 : s 244 = [])
    (h245 : s 245 = []) (h251 : s 251 = []) (h252 : s 252 = []) :
    ExecutesIn (iteration multiply add) (Km + Ka + 50 * W + 47) s
      (Function.update (Function.update s 246 rest) 240
        (encode (stepValue mulOp addOp x a c))) := by
  let p := mulOp a x
  let v := stepValue mulOp addOp x a c
  let s1 := Function.update s 241 (encode x)
  let s2 := Function.update s1 240 (encode p)
  let s3 := Function.update s2 241 []
  let s4 := Function.update (Function.update s3 246 rest) 241 (encode c)
  let s5 := Function.update s4 240 (encode v)
  have hf1 : LowFrame base s1 := lowFrame_update hf 241 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf1 240 (by decide) _
  have hf3 : LowFrame base s3 := lowFrame_update hf2 241 (by decide) _
  have hf4 : LowFrame base s4 := lowFrame_update
    (lowFrame_update hf3 246 (by decide) _) 241 (by decide) _
  have h1 : ExecutesIn (copy 247 241) (7 * W + 5) s s1 := by
    simpa [s1, hx, h241, hwidth] using copy_run 247 241 s
      (by decide) (by decide) (by decide) h120
  have h2 : ExecutesIn (binaryStep multiply) (Km + 8 * W + 9) s1 s2 :=
    binaryStep_run base encode multiply mulOp Km W hm (fun a => (hwidth a).le)
      s1 a x hf1 (by simp [s1, hacc]) (by simp [s1])
      (by simp [s1, h244]) (by simp [s1, h245])
  have h3 : ExecutesIn (clear 241) (2 * W + 3) s2 s3 := by
    simpa [s3, s2, s1, hwidth] using clear_run 241 s2
  have h4 : ExecutesIn takeCoefficient (23 * W + 18) s3 s4 := by
    simpa only [hwidth] using takeCoefficient_run s3 (encode c) rest
      (by simp [s3, s2, s1, hs]) (by simp [s3, s2, s1, hw, hwidth])
      (by simp [s3]) (by simp [s3, s2, s1, h251])
      (by simp [s3, s2, s1, h252])
  have h5 : ExecutesIn (binaryStep add) (Ka + 8 * W + 9) s4 s5 :=
    binaryStep_run base encode add addOp Ka W ha (fun a => (hwidth a).le)
      s4 p c hf4 (by simp [s4, s3, s2]) (by simp [s4])
      (by simp [s4, s3, s2, s1, h244]) (by simp [s4, s3, s2, s1, h245])
  have he : Function.update s5 241 [] =
      Function.update (Function.update s 246 rest) 240 (encode v) := by
    funext i
    by_cases h240 : i = 240 <;> by_cases h241' : i = 241 <;>
      by_cases h246 : i = 246 <;>
      simp [s5, s4, s3, s2, s1, h240, h241', h246, h241]
  have h6 : ExecutesIn (clear 241) (2 * W + 3) s5
      (Function.update (Function.update s 246 rest) 240 (encode v)) := by
    have h := clear_run 241 s5
    rw [he] at h
    simpa [s5, s4, hwidth] using h
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
  convert h using 1 <;> first | omega | rfl

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms

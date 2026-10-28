import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationMaskProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram

namespace OAI.Algorithms

/-! Emit the computed beta at the actual all-zero sparse key. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

def originKey (n : ℕ) : List Bool :=
  PerturbationEmitProgram.keyBits (List.replicate n false) 0

def origin : Code := .seq PerturbationMaskProgram.zeroCommand
  (.seq PerturbationEmitProgram.keyCommand (.seq (copy 220 228)
    (.seq (.call (StackRoutines.reverseProgram 228 226 227 (0 : Fin 16) 1))
      (.seq PerturbationEmitProgram.emitCommand (clear 214)))))

def originScratch : List (Fin 256) := [120,214,221,222,223,224,226,227,228]

theorem origin_run (s : Store) (n : ℕ) (hn : (s 212).length=n)
    (he : ∀ i ∈ originScratch,s i=[]) :
    ExecutesIn origin (33*n+20*(s 220).length+83) s
      (Function.update s 217 (Encoding.frame (originKey n)++Encoding.frame (s 220)++s 217)) := by
  let s1 := Function.update s 214 (List.replicate n false)
  let s2 := Function.update s1 222 (originKey n).reverse
  let s3 := Function.update s2 228 (s 220)
  let s4 := Function.update s2 228 (s 220).reverse
  let s5 := Function.update s1 217
    (Encoding.frame (originKey n)++Encoding.frame (s 220)++s 217)
  have hl : (originKey n).length=n+2 := by
    simp [originKey,PerturbationEmitProgram.keyBits,PerturbationProgram.Key.bits]
  have h1 : ExecutesIn PerturbationMaskProgram.zeroCommand (11*n+7) s s1 :=
    PerturbationMaskProgram.zero_run s n hn (he 120 (by simp [originScratch]))
      (he 221 (by simp [originScratch])) (he 214 (by simp [originScratch]))
  have h2 : ExecutesIn PerturbationEmitProgram.keyCommand (16*n+40) s1 s2 := by
    have h := PerturbationEmitProgram.key_run s1 (List.replicate n false) 0
      (by simp [s1]) (by simpa [s1] using he 221 (by simp [originScratch]))
      (by simpa [s1] using he 120 (by simp [originScratch]))
      (by simpa [s1] using he 222 (by simp [originScratch]))
      (by simpa [s1] using he 223 (by simp [originScratch]))
      (by simpa [s1] using he 224 (by simp [originScratch]))
    simpa [s2,originKey] using h
  have h3 : ExecutesIn (copy 220 228) (7*(s 220).length+5) s2 s3 := by
    simpa [s3,s2,s1,he 228 (by simp [originScratch])] using
      copy_run 220 228 s2 (by decide) (by decide) (by decide)
        (by simpa [s2,s1] using he 120 (by simp [originScratch]))
  have h4 : ExecutesIn (.call (StackRoutines.reverseProgram 228 226 227 (0 : Fin 16) 1))
      (9*(s 220).length+7) s3 s4 := by
    intro regs
    have h := reverse_eval (⟨regs,s3⟩ : Data) 228 226 227 0 1
      (by decide) (by decide) (by decide) (by decide)
      (by simpa [s3,s2,s1] using he 226 (by simp [originScratch]))
      (by simpa [s3,s2,s1] using he 227 (by simp [originScratch]))
    exact ⟨9*(s 220).length+7,_,le_rfl,by simpa [s4,s3,afterReverse,StackRoutines.reverseStacks] using h⟩
  have hout : Function.update (Function.update (Function.update s4 222 []) 228 [])
      217 (Encoding.frame (originKey n)++Encoding.frame (s 220)++s4 217)=s5 := by
    funext i
    by_cases h214 : i=214 <;> by_cases h217 : i=217 <;> by_cases h222 : i=222 <;>
      by_cases h228 : i=228 <;>
      simp [s5,s4,s2,s1,h214,h217,h222,h228,
        he 222 (by simp [originScratch]),he 228 (by simp [originScratch])]
  have h5 : ExecutesIn PerturbationEmitProgram.emitCommand
      (4*(n+2)+4*(s 220).length+13) s4 s5 := by
    have h := PerturbationEmitProgram.emit_run s4 (originKey n) (s 220)
      (by simp [s4,s2]) (by simp [s4])
    rw [hout,hl] at h
    exact h
  have hout2 : Function.update s5 214 []=Function.update s 217
      (Encoding.frame (originKey n)++Encoding.frame (s 220)++s 217) := by
    funext i
    by_cases h214 : i=214 <;> by_cases h217 : i=217 <;>
      simp [s5,s1,h214,h217,he 214 (by simp [originScratch])]
  have h6 := clear_run 214 s5
  rw [hout2] at h6
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
  convert h using 1 <;> first | rfl | (simp [s5, s1] ; ring)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms

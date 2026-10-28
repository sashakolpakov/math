import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram

namespace OAI.Algorithms

/-! Paid preserving copies of every beta master and explicit scratch cleanup. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl

def initialized (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update s
    230 (s 205)) 231 (s 206)) 220 (s 207)) 247 (s 209)) 250 (s 211)

def initBudget (s : Store) : ℕ :=
  7*(s 205).length+7*(s 206).length+7*(s 207).length+
    7*(s 209).length+7*(s 211).length+25

theorem prepareInput_run (s : Store) (h120 : s 120=[])
    (h230 : s 230=[]) (h231 : s 231=[]) (h220 : s 220=[])
    (h247 : s 247=[]) (h250 : s 250=[]) :
    ExecutesIn prepareInput (initBudget s) s (initialized s) := by
  let s1 := Function.update s 230 (s 205)
  let s2 := Function.update s1 231 (s 206)
  let s3 := Function.update s2 220 (s 207)
  let s4 := Function.update s3 247 (s 209)
  let s5 := Function.update s4 250 (s 211)
  have h1 : ExecutesIn (copy 205 230) (7*(s 205).length+5) s s1 := by
    simpa [s1,h230] using copy_run 205 230 s
      (by decide) (by decide) (by decide) h120
  have h2 : ExecutesIn (copy 206 231) (7*(s 206).length+5) s1 s2 := by
    simpa [s2,s1,h231] using copy_run 206 231 s1
      (by decide) (by decide) (by decide) (by simp [s1,h120])
  have h3 : ExecutesIn (copy 207 220) (7*(s 207).length+5) s2 s3 := by
    simpa [s3,s2,s1,h220] using copy_run 207 220 s2
      (by decide) (by decide) (by decide) (by simp [s2,s1,h120])
  have h4 : ExecutesIn (copy 209 247) (7*(s 209).length+5) s3 s4 := by
    simpa [s4,s3,s2,s1,h247] using copy_run 209 247 s3
      (by decide) (by decide) (by decide) (by simp [s3,s2,s1,h120])
  have h5 : ExecutesIn (copy 211 250) (7*(s 211).length+5) s4 s5 := by
    simpa [s5,s4,s3,s2,s1,h250] using copy_run 211 250 s4
      (by decide) (by decide) (by decide) (by simp [s4,s3,s2,s1,h120])
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  convert h using 1 <;> first | (simp only [initBudget]; omega) | rfl

def finished (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update s 230 []) 231 []) 247 []) 250 []

def finishBudget (s : Store) : ℕ :=
  2*(s 230).length+2*(s 231).length+2*(s 247).length+2*(s 250).length+12

theorem finish_run (s : Store) : ExecutesIn finish (finishBudget s) s (finished s) := by
  have h1 := clear_run 230 s
  have h2 := clear_run 231 (Function.update s 230 [])
  have h3 := clear_run 247 (Function.update (Function.update s 230 []) 231 [])
  have h4 := clear_run 250 (Function.update (Function.update (Function.update s 230 []) 231 []) 247 [])
  have h := h1.seq (h2.seq (h3.seq h4))
  convert h using 1 <;> first | (simp [finishBudget]; omega) | rfl

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms

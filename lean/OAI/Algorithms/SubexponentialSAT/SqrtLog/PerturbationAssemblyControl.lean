import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgramStage

namespace OAI.Algorithms

/-! Fixed native staging for the complete per-coordinate perturbation worker.
All dimensions and values are runtime tapes. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor

/-- Current source row219, full source count210, scalar width211. -/
def loadRow : Code := .seq (move 219 246) (.seq (copy 210 248) (copy 211 250))

def loaded (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update s 219 [])
    246 (s 219)) 248 (s 210)) 250 (s 211)

theorem loadRow_run (s : Store) (h120 : s 120=[]) (h245 : s 245=[])
    (h246 : s 246=[]) (h248 : s 248=[]) (h250 : s 250=[]) :
    ExecutesIn loadRow (6*(s 219).length+7*(s 210).length+7*(s 211).length+16)
      s (loaded s) := by
  let s1 := Function.update (Function.update s 219 []) 246 (s 219)
  let s2 := Function.update s1 248 (s 210)
  have h1 : ExecutesIn (move 219 246) (6*(s 219).length+6) s s1 :=
    move_run s 219 246 (by decide) (by decide) (by decide) h245 h246
  have h2 : ExecutesIn (copy 210 248) (7*(s 210).length+5) s1 s2 := by
    simpa [s1,s2,h248] using copy_run 210 248 s1 (by decide) (by decide) (by decide)
      (by simp [s1,h120])
  have h3 : ExecutesIn (copy 211 250) (7*(s 211).length+5) s2 (loaded s) := by
    simpa [s1,s2,loaded,h250] using copy_run 211 250 s2 (by decide) (by decide) (by decide)
      (by simp [s2,s1,h120])
  convert h1.seq (h2.seq h3) using 1 <;> first | rfl | omega

/-- Padded stream240 goes to246. The source count is reset from210. The target
zero array192 supplies both seed240 and polynomial-cell width250. -/
def enterHorner : Code := .seq (move 240 246) (.seq (copy 210 248)
  (.seq (clear 250) (.seq (copy 192 250) (copy 192 240))))

def hornerInput (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update s
    240 (s 192)) 246 (s 240)) 248 (s 210)) 250 (s 192)

theorem enterHorner_run (s : Store) (h120 : s 120=[]) (h245 : s 245=[])
    (h246 : s 246=[]) (h248 : s 248=[]) :
    ExecutesIn enterHorner
      (6*(s 240).length+7*(s 210).length+2*(s 250).length+14*(s 192).length+24)
      s (hornerInput s) := by
  let s1 := Function.update (Function.update s 240 []) 246 (s 240)
  let s2 := Function.update s1 248 (s 210)
  let s3 := Function.update s2 250 []
  let s4 := Function.update s3 250 (s 192)
  have h1 : ExecutesIn (move 240 246) (6*(s 240).length+6) s s1 :=
    move_run s 240 246 (by decide) (by decide) (by decide) h245 h246
  have h2 : ExecutesIn (copy 210 248) (7*(s 210).length+5) s1 s2 := by
    simpa [s1,s2,h248] using copy_run 210 248 s1 (by decide) (by decide) (by decide)
      (by simp [s1,h120])
  have h3 : ExecutesIn (clear 250) (2*(s 250).length+3) s2 s3 := by
    simpa [s1,s2,s3] using clear_run 250 s2
  have h4 : ExecutesIn (copy 192 250) (7*(s 192).length+5) s3 s4 := by
    simpa [s1,s2,s3,s4] using copy_run 192 250 s3 (by decide) (by decide) (by decide)
      (by simp [s3,s2,s1,h120])
  have he : Function.update s4 240 ((s4 192)++s4 240)=hornerInput s := by
    funext i
    by_cases h240 : i=240 <;> by_cases h246 : i=246 <;>
      by_cases h248 : i=248 <;> by_cases h250 : i=250 <;>
      simp [s4,s3,s2,s1,hornerInput,h240,h246,h248,h250]
  have h5 : ExecutesIn (copy 192 240) (7*(s 192).length+5) s4 (hornerInput s) := by
    have h := copy_run 192 240 s4 (by decide) (by decide) (by decide)
      (by simp [s4,s3,s2,s1,h120])
    rw [he] at h
    simpa [s4,s3,s2,s1] using h
  convert h1.seq (h2.seq (h3.seq (h4.seq h5))) using 1 <;> first | rfl | omega

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms

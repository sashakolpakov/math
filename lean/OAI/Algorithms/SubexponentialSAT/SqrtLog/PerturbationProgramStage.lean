import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgramPaddingRun

namespace OAI.Algorithms

/-! Exact staging from the source polynomial executor ABI to the padding ABI.
The node and protected arithmetic caches are unchanged. -/
namespace SubexponentialSAT.SqrtLog.PerturbationProgram.Padding
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor

/-- Consume the source coefficient stream on240; copy its protected runtime
coefficient count193. Ports246/248 are the padding input stream/count. -/
def stageInput : Code := .seq (move 240 246) (copy 193 248)

theorem stageInput_run (s : Store) (h120 : s 120=[]) (h245 : s 245=[])
    (h246 : s 246=[]) (h248 : s 248=[]) :
    ExecutesIn stageInput (6*(s 240).length+7*(s 193).length+11) s
      (Function.update (Function.update (Function.update s 240 [])
        246 (s 240)) 248 (s 193)) := by
  let s1 := Function.update (Function.update s 240 []) 246 (s 240)
  have h1 : ExecutesIn (move 240 246) (6*(s 240).length+6) s s1 := by
    exact move_run s 240 246 (by decide) (by decide) (by decide) h245 h246
  have h2 : ExecutesIn (copy 193 248) (7*(s 193).length+5) s1
      (Function.update s1 248 (s 193)) := by
    simpa [s1,h248] using copy_run 193 248 s1 (by decide) (by decide) (by decide)
      (by simp [s1,h120])
  convert h1.seq h2 using 1 <;> first | omega | rfl

end SubexponentialSAT.SqrtLog.PerturbationProgram.Padding

end OAI.Algorithms

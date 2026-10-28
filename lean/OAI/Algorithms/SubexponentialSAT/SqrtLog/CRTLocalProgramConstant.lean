import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramCall

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def constantCommand : Code :=
  .seq (copy 223 247) (.seq (takeCell 247 205) (clear 247))

theorem constantCommand_run (s : Store) (constant rest : List Bool)
    (harray : s 223 = constant ++ rest)
    (hwidth : (s 104).length = constant.length)
    (h120 : s 120 = []) (h121 : s 121 = []) (h122 : s 122 = [])
    (h247 : s 247 = []) (h205 : s 205 = []) :
    ExecutesIn constantCommand (21*constant.length+9*rest.length+19) s
      (Function.update s 205 constant) := by
  let s1 := Function.update s 247 (constant ++ rest)
  let s2 := Function.update (Function.update s 247 rest) 205 constant
  have h1 : ExecutesIn (copy 223 247) (7*(constant.length+rest.length)+5) s s1 := by
    simpa [s1, harray, h247] using copy_run 223 247 s
      (by decide) (by decide) (by decide) h120
  have h2 : ExecutesIn (takeCell 247 205) (14*constant.length+11) s1 s2 := by
    simpa [s1, s2, h205] using takeCell_run 247 205 s1 constant rest
      (by decide) (by simp [s1]) (by simp [s1, h121]) (by simp [s1, h122])
      (by simpa [s1] using hwidth)
  have he : Function.update s2 247 [] = Function.update s 205 constant := by
    funext i
    by_cases hi : i = 247 <;> simp [s2, Function.update_apply, hi, h247]
  have h3 : ExecutesIn (clear 247) (2*rest.length+3) s2 (Function.update s 205 constant) := by
    have h := clear_run 247 s2
    rw [he] at h
    simpa [s2] using h
  convert h1.seq (h2.seq h3) using 1
  · rfl
  · ring

/-- All coefficient-to-polynomial padding is performed by native constructor
loops. The scalar inverse uses t, while each constructor uses J. -/
def inverseConstantsCommand (sm sa : Code) : Code :=
  .seq (inverseCommand sm sa)
    (.seq (callAt sm 208 211 205)
      (.seq (SubexpPolynomialConstructor.construct 208 104 227)
        (.seq (SubexpPolynomialConstructor.construct 205 104 228)
          (SubexpLocalCRTSetup.clearMany [205,208]))))

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms

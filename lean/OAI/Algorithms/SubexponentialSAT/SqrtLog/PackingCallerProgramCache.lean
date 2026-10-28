import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open PackingLoaderProgram

def cacheInputs : Code := .seq (saveHigh 10 53) (saveHigh 39 54)
def cached (outside : Store) (width alphabet : List Bool) : Store :=
  Function.update (Function.update outside 53 width) 54 alphabet

theorem cacheInputs_eval (outside : Store) (d : Small)
    (h52 : outside 52=[]) (h53 : outside 53=[]) (h54 : outside 54=[]) :
    ∃ rf, Eval cacheInputs (7*(d.stacks 10).length+5+(7*(d.stacks 39).length+5))
      (framed outside d)
      (framed (cached outside (d.stacks 10) (d.stacks 39)) (setRegs d rf)) := by
  obtain ⟨r1,h1⟩ := saveHigh_eval outside d 10 53 (by decide) (by decide) h52 h53
  obtain ⟨r2,h2⟩ := saveHigh_eval (Function.update outside 53 (d.stacks 10)) (setRegs d r1)
    39 54 (by decide) (by decide) (by simpa using h52) (by simpa using h54)
  exact ⟨r2,h1.seq h2⟩

@[simp] theorem cached_52 (outside : Store) (width alphabet : List Bool) :
    cached outside width alphabet 52=outside 52 := by simp [cached]
@[simp] theorem cached_width (outside : Store) (width alphabet : List Bool) :
    cached outside width alphabet 53=width := by simp [cached]
@[simp] theorem cached_alphabet (outside : Store) (width alphabet : List Bool) :
    cached outside width alphabet 54=alphabet := by simp [cached]

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms

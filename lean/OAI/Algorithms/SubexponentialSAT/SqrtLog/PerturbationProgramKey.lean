import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgramABI
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionStore

namespace OAI.Algorithms

/-! Native construction of a positive-Z singleton key from its runtime unary
exponent and support mask. The reversed result feeds the sparse record emitter. -/
namespace SubexponentialSAT.SqrtLog.PerturbationProgram.Key
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

def pushFalse : Code := Subexp.TupleProgram.pushConst 222 0 false

theorem pushFalse_run (s : Store) : ExecutesIn pushFalse 2 s
    (Function.update s 222 (false::s 222)) := by
  intro regs
  refine ⟨2,Function.update regs 0 false,le_refl _,?_⟩
  simpa [pushFalse,Subexp.TupleProgram.pushedState] using
    Subexp.TupleProgram.pushConst_eval (222 : Fin 256) (0 : Fin 16) false
      (⟨regs,s⟩ : Data)

def command : Code := .seq (copy 220 222) (.seq pushFalse
  (.seq (copy 221 222) (.seq pushFalse
    (.call (StackRoutines.reverseProgram 222 223 224 (0 : Fin 16) 1)))))

def bits (unary mask : List Bool) : List Bool := false::(unary++(false::mask))

theorem command_run (s : Store) (unary mask : List Bool)
    (hu : s 221=unary) (hm : s 220=mask) (h120 : s 120=[])
    (h222 : s 222=[]) (h223 : s 223=[]) (h224 : s 224=[]) :
    ExecutesIn command (16*(unary.length+mask.length)+39) s
      (Function.update s 222 (bits unary mask).reverse) := by
  let s1 := Function.update s 222 mask
  let s2 := Function.update s 222 (false::mask)
  let s3 := Function.update s 222 (unary++false::mask)
  let s4 := Function.update s 222 (bits unary mask)
  have h1 : ExecutesIn (copy 220 222) (7*mask.length+5) s s1 := by
    simpa [s1,hm,h222] using copy_run 220 222 s (by decide) (by decide) (by decide) h120
  have h2 : ExecutesIn pushFalse 2 s1 s2 := by
    simpa [s1,s2] using pushFalse_run s1
  have h3 : ExecutesIn (copy 221 222) (7*unary.length+5) s2 s3 := by
    simpa [s2,s3,hu] using copy_run 221 222 s2 (by decide) (by decide) (by decide)
      (by simp [s2,h120])
  have h4 : ExecutesIn pushFalse 2 s3 s4 := by
    simpa [s3,s4,bits] using pushFalse_run s3
  have h5 : ExecutesIn (.call (StackRoutines.reverseProgram 222 223 224 (0 : Fin 16) 1))
      (9*(unary.length+mask.length+2)+7) s4
      (Function.update s 222 (bits unary mask).reverse) := by
    intro regs
    have h := reverse_eval (⟨regs,s4⟩ : Data) 222 223 224 0 1
      (by decide) (by decide) (by decide) (by decide)
      (by simp [s4,h223]) (by simp [s4,h224])
    refine ⟨9*(bits unary mask).length+7,readRegs regs 0 1 none,?_,?_⟩
    · simp [bits]; omega
    · simpa [s4,afterReverse,StackRoutines.reverseStacks] using h
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  convert h using 1 <;> first | omega | rfl

theorem singleton_run {n : ℕ} (s : Store) (v : Fin n) (j : ℕ)
    (hu : s 221=List.replicate j true) (hm : s 220=Squarefree.encodeMask {v})
    (h120 : s 120=[]) (h222 : s 222=[]) (h223 : s 223=[]) (h224 : s 224=[]) :
    ExecutesIn command (16*(j+n)+39) s
      (Function.update s 222 (Squarefree.encodeIndex (⟨0,j,{v}⟩ : Squarefree.Index (Fin n))).reverse) := by
  have h := command_run s (List.replicate j true) (Squarefree.encodeMask {v})
    hu hm h120 h222 h223 h224
  simpa [bits,Squarefree.encodeIndex,Encoding.encodeNat,List.append_assoc] using h

end SubexponentialSAT.SqrtLog.PerturbationProgram.Key

end OAI.Algorithms

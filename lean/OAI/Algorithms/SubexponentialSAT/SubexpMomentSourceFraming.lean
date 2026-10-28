import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlockAssemblyTraversal
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Byte packing used while replacing unweighted descriptors by their
computed literals. Completed payloads are framed without adding a list
terminator; a list is terminated only at its own boundary. -/

namespace SubexponentialSAT.SubexpBlockAssembly

open BitProgram StructuredCalls
open SubexpKernelControl (Word)

local infixr:60 " ;; " => Cmd.seq

def packComplete (src dst : Fin 22) : Code :=
  transfer src 19 ;; appendRecord 19 dst ;; clear 19

def packUpdate (i j : Fin 7) (a : Buffers) : Buffers :=
  emit j (record (a i).reverse) (Function.update a i [])

theorem packComplete_work (i j : Fin 7) (v p c : Bool) (input zero one : Word)
    (a : Buffers) :
    Executes (packComplete (bufferPort i) (bufferPort j))
      (state v p c input zero one a)
      (state false false true input zero one (packUpdate i j a)) := by
  exact executes_seq (transferBuffer_work i v p c input zero one a)
    (executes_seq (appendRecord_work j false false c input zero one (a i).reverse
      (Function.update a i []))
      (clearPayload_work false false true input zero one (a i).reverse
        (emit j (record (a i).reverse) (Function.update a i []))))

def closeBare (src dst : Fin 22) : Code :=
  pushBit src false ;; transfer src 19 ;; transfer 19 dst

def bareUpdate (i j : Fin 7) (a : Buffers) : Buffers :=
  emit j (false :: a i).reverse (Function.update a i [])

theorem closeBare_work (i j : Fin 7) (v p c : Bool) (input zero one : Word)
    (a : Buffers) :
    Executes (closeBare (bufferPort i) (bufferPort j))
      (state v p c input zero one a)
      (state false false c input zero one (bareUpdate i j a)) := by
  let b := Function.update a i (false :: a i)
  have h := executes_seq (pushBuffer_work i false v p c input zero one a)
    (executes_seq (transferBuffer_work i false p c input zero one b)
      (transferPayload_work j false false c input zero one (b i).reverse
        (Function.update b i [])))
  simpa only [closeBare,bareUpdate,b,Function.update_same,Function.update_idem] using h

theorem appendFrame_work (i : Fin 7) (v p c : Bool)
    (input zero one payload : Word) (a : Buffers) :
    Executes (appendFrame 19 (bufferPort i))
      (work v p c input zero one a payload [])
      (work false false true input zero one (emit i (Encoding.frame payload) a) payload []) := by
  have h := appendFrame_exec 19 (bufferPort i)
    (by fin_cases i <;> decide) (by decide) (by fin_cases i <;> decide)
    (work v p c input zero one a payload []) rfl
  have he : afterFrame (bufferPort i) payload (work v p c input zero one a payload []) =
      work false false true input zero one (emit i (Encoding.frame payload) a) payload [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j; fin_cases i <;> fin_cases j <;>
        simp [work,emit,bufferPort]
  change Executes _ _ (afterFrame (bufferPort i) payload
    (work v p c input zero one a payload [])) at h
  rw [he] at h
  exact h

/-- The completed payload is framed once. No additional false bit is
inserted into that payload. -/
theorem packUpdate_emitted (i j : Fin 7) (a : Buffers) (bits : Word)
    (hi : a i = []) :
    packUpdate i j (emit i bits a) = emit j (record bits) a := by
  have hz : Function.update a i [] = a := by
    rw [←hi,Function.update_eq_self]
  simp [packUpdate,emit,hi,hz,Function.update_idem]

/-- Closing a list appends precisely its false terminator before copying
the resulting bytes into the enclosing payload. -/
theorem bareUpdate_emitted (i j : Fin 7) (a : Buffers) (bits : Word)
    (hi : a i = []) :
    bareUpdate i j (emit i bits a) = emit j (bits ++ [false]) a := by
  have hz : Function.update a i [] = a := by
    rw [←hi,Function.update_eq_self]
  simp [bareUpdate,emit,hi,hz,Function.update_idem,List.reverse_cons,List.reverse_append]

end SubexponentialSAT.SubexpBlockAssembly

end OAI.Algorithms

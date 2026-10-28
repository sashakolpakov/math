import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgramCore

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def pairBytes (v f : ℕ) : List Bool :=
  ProgramEncoding.encodeRecords [unary v,unary f]
def pairPayload (v f : ℕ) : List Bool := Encoding.frame (pairBytes v f)
def pairTail (f : ℕ) : List Bool := true :: (Encoding.frame (unary f) ++ [false])

@[simp] theorem pairBytes_length (v f : ℕ) : (pairBytes v f).length=2*v+2*f+5 := by
  simp [pairBytes,ProgramEncoding.encodeRecords,Encoding.encodeList,Encoding.length_frame]
  omega

@[simp] theorem pairPayload_length (v f : ℕ) : (pairPayload v f).length=4*v+4*f+11 := by
  simp [pairPayload,Encoding.length_frame]
  omega

@[simp] theorem pairTail_length (f : ℕ) : (pairTail f).length=2*f+3 := by
  simp [pairTail,Encoding.length_frame]

theorem pairPayload_original (v f : ℕ) :
    pairPayload v f=SubexponentialSAT.Subexp.PackingVertexLabels.planPayload [v,f] := rfl

def parseOwner : Code := .seq forward (.seq readFrame (.seq forward
  (.seq popDecoded (.seq readFrame (clear 4)))))

/-- The second address is consumed and charged; only the original owner word
is exposed to the comparison stage. The outer scan tail is preserved. -/
theorem parseOwner_eval (regs : Fin 5 → Bool) (v f : ℕ)
    (q m s i a c o : List Bool) :
    Eval parseOwner (36*v+34*f+102)
      (data regs q m s (pairPayload v f).reverse [] [] [] i a c o)
      (data (status regs false false) q m s (unary v) [] [] [] i a c o) := by
  have h1 := forward_eval regs q m s (pairPayload v f) [] [] i a c o
  have h2 := readFrame_eval (status regs false false) q m s (pairBytes v f) [] [] [] i a c o
  have h3 := forward_eval (status regs false true) q m s (pairBytes v f) [] [] i a c o
  have h4 := popDecoded_eval (status regs false false) true q m s []
    (Encoding.frame (unary v)++pairTail f) [] [] i a c o
  have h5 := readFrame_eval (status regs true true) q m s (unary v) (pairTail f) [] [] i a c o
  have h6 := clear_eval 4 (data (status regs false true) q m s (unary v) (pairTail f) [] [] i a c o)
  have h6e : cleared (data (status regs false true) q m s (unary v) (pairTail f)
      [] [] i a c o) 4 = data (status regs false false) q m s (unary v) [] [] [] i a c o := by
    apply state_ext
    · simp [cleared,data]
    · funext j; fin_cases j <;> simp [cleared,data]
  rw [h6e] at h6
  have hvrev : (unary v).reverse=unary v := by simp
  simp only [status_status,List.append_nil,hvrev] at h2 h3 h4 h5
  have hp : pairBytes v f=true::(Encoding.frame (unary v)++pairTail f) := rfl
  rw [hp] at h3
  have hh := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
  convert hh using 1 <;>
    simp [parseOwner,pairPayload,pairBytes,pairTail,ProgramEncoding.encodeRecords,
      Encoding.encodeList,Encoding.length_frame,data] ; omega

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms

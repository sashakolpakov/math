import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgramPadding

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationProgram.Padding
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

def command : Code := .seq HornerProgram.reverseStream (Traversal.command iteration)

def budget (N D W : ℕ) : ℕ := 9*(N*W)+7 + (N*(260*(D+1)*(W+1)+2)+2)

def output {C : Type*} (encode : C → List Bool) (D W : ℕ) (cs : List C) : List Bool :=
  cs.flatMap fun c => cell D W (encode c)

theorem output_length {C : Type*} (encode : C → List Bool) (D W : ℕ)
    (hwidth : ∀ c, (encode c).length=W) (cs : List C) :
    (output encode D W cs).length=cs.length*D*W := by
  induction cs with
  | nil => simp [output]
  | cons c cs ih =>
      change (cell D W (encode c)++output encode D W cs).length=_
      rw [List.length_append,cell_length D W _ (hwidth c),ih]
      simp only [List.length_cons]
      ring

theorem budget_polynomial (N D W : ℕ) :
    budget N D W ≤ 280*(N+1)*(D+1)*(W+1) := by
  unfold budget
  ring_nf
  omega

/-- Full native construction of the homogeneous stream required by polynomial
Horner, from the actual serialized scalar coefficient array. No padded-input
oracle is assumed: both all zero bits and every copied coefficient are paid. -/
theorem command_run {C : Type*} (base : Store) (encode : C → List Bool)
    (D W : ℕ) (hwidth : ∀ c, (encode c).length=W)
    (cs : List C) (hcs : base 246=HornerProgram.encodePolynomial encode cs)
    (hacc : base 240=[]) (hcount : (base 248).length=cs.length)
    (hw : (base 250).length=W) (hD : base 243=List.replicate D true)
    (hzero : base 104=List.replicate W false) (hz : base 254=List.replicate W false)
    (h100 : base 100=[]) (h101 : base 101=[]) (h102 : base 102=[])
    (h107 : base 107=[]) (h108 : base 108=[]) (h120 : base 120=[])
    (h241 : base 241=[]) (h245 : base 245=[]) (h251 : base 251=[])
    (h252 : base 252=[]) (h253 : base 253=[]) :
    ExecutesIn command (budget cs.length D W) base
      (Function.update (Function.update (Function.update base 246 [])
        240 (output encode D W cs)) 248 []) := by
  let s := Function.update base 246 (HornerProgram.backward encode cs.reverse)
  have hr : ExecutesIn HornerProgram.reverseStream (9*(cs.length*W)+7) base s := by
    intro regs
    have h := reverse_eval (⟨regs,base⟩ : Data) 246 251 252 0 1
      (by decide) (by decide) (by decide) (by decide) h251 h252
    refine ⟨9*(base 246).length+7,readRegs regs 0 1 none,?_,?_⟩
    · rw [hcs,HornerProgram.encodePolynomial_length encode W hwidth]
    · simpa [HornerProgram.reverseStream,afterReverse,StackRoutines.reverseStacks,s,hcs,
        HornerProgram.reverse_encodePolynomial] using h
  have hl := streaming_run s encode D W hwidth
    (by simp [s,hw]) (by simp [s,hD]) (by simp [s,hzero]) (by simp [s,hz])
    (by simp [s,h100]) (by simp [s,h101]) (by simp [s,h102])
    (by simp [s,h107]) (by simp [s,h108]) (by simp [s,h120])
    (by simp [s,h241]) (by simp [s,h245]) (by simp [s,h251])
    (by simp [s,h252]) (by simp [s,h253]) cs.reverse [] (base 248)
    (by simpa using hcount)
  have hin : Traversal.ready s encode cs.reverse [] (base 248)=s := by
    funext i
    by_cases h240 : i=240 <;> by_cases h246 : i=246 <;> by_cases h248 : i=248 <;>
      simp [Traversal.ready,s,h240,h246,h248,hacc]
  have hout : Traversal.ready s encode [] (cs.reverse.foldl (step encode D W) []) [] =
      Function.update (Function.update (Function.update base 246 [])
        240 (output encode D W cs)) 248 [] := by
    rw [fold_output]
    simp [Traversal.ready,s,output,HornerProgram.backward,SubexpHornerControl.backward]
  rw [hin,hout,List.length_reverse] at hl
  exact hr.seq hl

end SubexponentialSAT.SqrtLog.PerturbationProgram.Padding

end OAI.Algorithms

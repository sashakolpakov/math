import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgramTraversal
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramConstructor
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram

namespace OAI.Algorithms

/-! Explicit finite scalar-to-polynomial padding. The runtime degree and
coefficient width are tapes, so this command is independent of all dimensions. -/
namespace SubexponentialSAT.SqrtLog.PerturbationProgram.Padding
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open DensePolynomialProgram.Constructor

/-- Read a scalar, build its padded constant polynomial, prepend that cell to
an accumulating output stream, and restore every temporary stack. -/
def iteration : Code :=
  .seq HornerProgram.takeCoefficient
    (.seq (SubexpPolynomialConstructor.construct 241 254 253)
      (.seq (clear 241) (.seq (copy 253 240) (clear 253))))

def cell (D W : ℕ) (bits : List Bool) : List Bool :=
  Counter.paddedBits W bits (List.replicate W false) D

theorem cell_length (D W : ℕ) (bits : List Bool) (h : bits.length=W) :
    (cell D W bits).length = D*W :=
  Counter.paddedBits_length D W bits _ h (by simp)

theorem iteration_run (s : Store) (D W : ℕ) (bits rest : List Bool)
    (hbits : bits.length=W) (hs : s 246=bits.reverse++rest)
    (hw : (s 250).length=W) (hD : s 243=List.replicate D true)
    (hzero : s 104=List.replicate W false) (hz : s 254=List.replicate W false)
    (h100 : s 100=[]) (h101 : s 101=[]) (h102 : s 102=[])
    (h107 : s 107=[]) (h108 : s 108=[]) (h120 : s 120=[])
    (h241 : s 241=[]) (h245 : s 245=[]) (h251 : s 251=[])
    (h252 : s 252=[]) (h253 : s 253=[]) :
    ExecutesIn iteration (260*(D+1)*(W+1)) s
      (Function.update (Function.update s 246 rest) 240 (cell D W bits++s 240)) := by
  let padded := cell D W bits
  let s1 := Function.update (Function.update s 246 rest) 241 bits
  let s2 := Function.update s1 253 padded
  let s3 := Function.update s2 241 []
  let s4 := Function.update s3 240 (padded++s 240)
  have h1 : ExecutesIn HornerProgram.takeCoefficient (23*W+18) s s1 := by
    simpa [s1,hbits] using HornerProgram.takeCoefficient_run s bits rest hs
      (hw.trans hbits.symm) h241 h251 h252
  have h2 : ExecutesIn (SubexpPolynomialConstructor.construct 241 254 253)
      (220*(D+1)*(W+1)) s1 s2 := by
    have h := construct_run s1 241 254 253 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) D W
      (by simp [s1,hbits]) (by simp [s1,hz])
      (by simp [s1,hD]) (by simp [s1,hzero])
      (by simp [s1,h100]) (by simp [s1,h101]) (by simp [s1,h102])
      (by simp [s1,h107]) (by simp [s1,h108]) (by simp [s1,h120])
      (by simp [s1,h245]) (by simp [s1,h253])
    simpa [s2,s1,padded,cell,hz] using h
  have h3 : ExecutesIn (clear 241) (2*W+3) s2 s3 := by
    simpa [s3,s2,s1,hbits] using clear_run 241 s2
  have h4 : ExecutesIn (copy 253 240) (7*(D*W)+5) s3 s4 := by
    simpa [s4,s3,s2,s1,padded,cell_length D W bits hbits] using
      copy_run 253 240 s3 (by decide) (by decide) (by decide)
        (by simp [s3,s2,s1,h120])
  have he : Function.update s4 253 [] =
      Function.update (Function.update s 246 rest) 240 (padded++s 240) := by
    funext i
    by_cases h240 : i=240 <;> by_cases h241' : i=241 <;>
      by_cases h246 : i=246 <;> by_cases h253' : i=253 <;>
      simp [s4,s3,s2,s1,h240,h241',h246,h253',h241,h253]
  have h5 : ExecutesIn (clear 253) (2*(D*W)+3) s4
      (Function.update (Function.update s 246 rest) 240 (padded++s 240)) := by
    have h := clear_run 253 s4
    rw [he] at h
    simpa [s4,s3,s2,padded,cell_length D W bits hbits] using h
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  apply h.mono
  nlinarith

def step {C : Type*} (encode : C → List Bool) (D W : ℕ)
    (acc : List Bool) (c : C) : List Bool := cell D W (encode c)++acc

theorem streaming_run {C : Type*} (base : Store) (encode : C → List Bool)
    (D W : ℕ) (hwidth : ∀ c, (encode c).length=W)
    (hw : (base 250).length=W) (hD : base 243=List.replicate D true)
    (hzero : base 104=List.replicate W false) (hz : base 254=List.replicate W false)
    (h100 : base 100=[]) (h101 : base 101=[]) (h102 : base 102=[])
    (h107 : base 107=[]) (h108 : base 108=[]) (h120 : base 120=[])
    (h241 : base 241=[]) (h245 : base 245=[]) (h251 : base 251=[])
    (h252 : base 252=[]) (h253 : base 253=[])
    (cs : List C) (acc count : List Bool) (hlen : count.length=cs.length) :
    ExecutesIn (Traversal.command iteration) (cs.length*(260*(D+1)*(W+1)+2)+2)
      (Traversal.ready base encode cs acc count)
      (Traversal.ready base encode [] (cs.foldl (step encode D W) acc) []) := by
  apply Traversal.run base encode iteration (step encode D W) (260*(D+1)*(W+1))
    _ cs acc count hlen
  intro c cs acc count
  let s := Traversal.ready base encode (c::cs) acc count
  have h := iteration_run s D W (encode c) (HornerProgram.backward encode cs)
    (hwidth c)
    (by simp [s,Traversal.ready,HornerProgram.backward,SubexpHornerControl.backward])
    (by simp [s,Traversal.ready,hw]) (by simp [s,Traversal.ready,hD])
    (by simp [s,Traversal.ready,hzero]) (by simp [s,Traversal.ready,hz])
    (by simp [s,Traversal.ready,h100]) (by simp [s,Traversal.ready,h101])
    (by simp [s,Traversal.ready,h102]) (by simp [s,Traversal.ready,h107])
    (by simp [s,Traversal.ready,h108]) (by simp [s,Traversal.ready,h120])
    (by simp [s,Traversal.ready,h241]) (by simp [s,Traversal.ready,h245])
    (by simp [s,Traversal.ready,h251]) (by simp [s,Traversal.ready,h252])
    (by simp [s,Traversal.ready,h253])
  convert h using 1
  funext i
  by_cases h240 : i=240 <;> by_cases h246 : i=246 <;> by_cases h248 : i=248 <;>
    simp [s,Traversal.ready,step,Function.update_apply,h240,h246,h248]

/-- Starting with highest degree first makes the final stream coefficient-zero first. -/
theorem fold_output {C : Type*} (encode : C → List Bool) (D W : ℕ) (cs : List C) :
    cs.reverse.foldl (step encode D W) [] = cs.flatMap (fun c => cell D W (encode c)) := by
  rw [List.foldl_reverse]
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [step,List.flatMap_def]

end SubexponentialSAT.SqrtLog.PerturbationProgram.Padding

end OAI.Algorithms

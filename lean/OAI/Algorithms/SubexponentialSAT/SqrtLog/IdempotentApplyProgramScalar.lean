import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramArrays
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramConstants

namespace OAI.Algorithms

/-! Native injection of a base coefficient into the first coordinate of an
extension-ring coefficient. The remaining coordinates are physically copied
from the canonical zero word. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpQuarticRing SubexpScanPrimitives
open IdempotentPreparationProgram

abbrev injectScalar : Cmd 8 41 :=
  .seq (paddedZeros 32 1) (.call (StackRoutines.copyProgram 31 32 2 (0 : Fin 8) 1))

abbrev scalarVector {B d : ℕ} (zero scalar : Word B) : RingProgram.Code (Word B) d :=
  fun i => if i.val=0 then scalar else zero

theorem scalarVector_flat {B d : ℕ} (hd : 0 < d) (zero scalar : Word B) :
    RingProgram.flat (scalarVector (d:=d) zero scalar) =
      scalar.val ++ Subexp.BlockCopyProgram.copies (d-1) zero.val := by
  simpa [scalarVector,Subexp.BlockCopyProgram.copies] using
    IdempotentProgram.flat_sparse hd scalar zero

theorem injectScalar_eval (d : Data) (dimension : ℕ) (hd : 0 < dimension)
    (hdegree : d.stacks 37=List.replicate dimension true)
    (h1 : d.stacks 1=[]) (h2 : d.stacks 2=[]) (hout : d.stacks 32=[]) :
    ∃ rf, Eval injectScalar
      (7*dimension+6+(dimension-1)*(7*(d.stacks 17).length+7)+6+
        (7*(d.stacks 31).length+5)) d
      ⟨rf,Function.update d.stacks 32
        (d.stacks 31 ++ Subexp.BlockCopyProgram.copies (dimension-1) (d.stacks 17))⟩ := by
  have heq : dimension-1+1=dimension := by omega
  obtain ⟨r1,hp⟩ := paddedZeros_eval d 32 1 (dimension-1)
    (by simpa [heq] using hdegree) h1 h2 (by decide) (by decide) (by decide)
  simp only [hout,List.append_nil,heq] at hp
  let a : Data := ⟨r1,Function.update d.stacks 32
    (Subexp.BlockCopyProgram.copies (dimension-1) (d.stacks 17))⟩
  have hc := copy_eval a 31 32 2 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simpa [a] using h2)
  have h := hp.seq hc
  refine ⟨(afterCopy a 31 32 0 1).regs,?_⟩
  convert h using 1 <;>
    simp [a,afterCopy,StackRoutines.copyStacks,Function.update_idem]
  ; omega

theorem injectScalar_words {B dimension : ℕ} (hd : 0 < dimension)
    (zero scalar : Word B) (d : Data)
    (hzero : d.stacks 17=zero.val) (hscalar : d.stacks 31=scalar.val)
    (hdegree : d.stacks 37=List.replicate dimension true)
    (h1 : d.stacks 1=[]) (h2 : d.stacks 2=[]) (hout : d.stacks 32=[]) :
    ∃ rf, Eval injectScalar
      (7*dimension+6+(dimension-1)*(7*B+7)+6+(7*B+5)) d
      ⟨rf,Function.update d.stacks 32 (RingProgram.flat (scalarVector (d:=dimension) zero scalar))⟩ := by
  simpa [hzero, hscalar, scalarVector_flat hd, zero.property, scalar.property] using
    injectScalar_eval d dimension hd hdegree h1 h2 hout

theorem scalarVector_denote (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {R : Type*} [CommRing R] (φ : ZMod (p^t) →+* R)
    {dimension : ℕ} (hd : 0 < dimension) (basis : Fin dimension → R)
    (hb : basis ⟨0,hd⟩=1) (word : RingProgram.ScalarCode p t) :
    RingProgram.denote (RingProgram.scalarRing p t M cache) φ basis
      (scalarVector cache.zero word) = φ (wordValue p t word) := by
  unfold RingProgram.denote
  rw [Finset.sum_eq_single ⟨0,hd⟩]
  · simp [scalarVector,RingProgram.scalarRing,hb]
  · intro i _ hi
    have hiv : i.val≠0 := by intro h; apply hi; exact Fin.ext h
    simp [scalarVector,hiv,RingProgram.scalarRing,cache.zero_correct]
  · simp

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms

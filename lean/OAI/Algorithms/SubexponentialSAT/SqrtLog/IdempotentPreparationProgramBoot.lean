import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramModulus

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls

def inputData (bits : List Bool) : Data :=
  ⟨fun _ => false,Function.update (fun _ => []) 31 bits⟩

def bootStacks (t : ℕ) (bits modulus logword : List Bool) : Fin 41 → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (fun _ => []) 31 bits) 29 (List.replicate t true))
    12 (List.replicate (2*t) true)) 37 (List.replicate (3*t) true)) 39 logword) 5 modulus

abbrev boot : Cmd 8 41 := .seq metadataFromBinary modulusCommand

theorem boot_eval (bits : List Bool) (t : ℕ) (hv : CounterPrograms.value bits=t) (ht : 0 < t) :
    ∃ (M : SubexpPreparedQuartic.Modulus 3 t), ∃ logword cost rf,
      CounterPrograms.value logword = Nat.clog 2 t ∧ logword.length ≤ bits.length+1 ∧
      cost ≤ 2001*(t+bits.length+2)^2 ∧
      Eval boot cost (inputData bits) ⟨rf,bootStacks t bits M.bits logword⟩ := by
  obtain ⟨logword,nm,rm,hlog,hlen,hnm,hm⟩ := metadataFromBinary_eval (inputData bits)
    (by simp [inputData]) (by simp [inputData]) (by simp [inputData])
    (by simp [inputData]) (by simp [inputData]) (by simp [inputData])
    (by simp [inputData]) (by simp [inputData]) (by simp [inputData])
    (by simp [inputData]) (by simp [inputData]) (by simpa [inputData,hv] using ht)
  let a : Data := ⟨rm,metadataStacks (inputData bits).stacks logword⟩
  have ready : ModulusWorkspaceEmpty a := by
    intro i hi
    fin_cases i <;> simp_all [a,metadataStacks,inputData,modulusPorts]
  have ha31 : a.stacks 31 = bits := by simp [a,metadataStacks,inputData]
  have hav : BinaryArithmetic.toNat (a.stacks 31) = t := by
    rw [ha31,←CounterPrograms.value_eq_toNat,hv]
  obtain ⟨M,np,rp,hnp,hp⟩ := modulusCommand_eval a ready
  let M' : SubexpPreparedQuartic.Modulus 3 t :=
    ⟨M.bits,by simpa only [hav] using M.length_le,by simpa only [hav] using M.value⟩
  rw [hav,ha31] at hnp
  refine ⟨M',logword,nm+np,rp,?_,?_,?_,?_⟩
  · simpa [inputData,hv] using hlog
  · simpa [inputData] using hlen
  · simp only [inputData,Function.update_same,hv] at hnm
    nlinarith
  · have he := hm.seq hp
    simpa [boot,a,metadataStacks,bootStacks,inputData,hv,M'] using he

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramMetadata
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramLog

namespace OAI.Algorithms

/-! The unary iteration budget is derived from the runtime binary t word.
This module includes its native conversion trace and preserves the original
word for modulus construction. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpScanPrimitives

def unaryPorts : Fin 3 → Fin 41 := ![28,29,30]

theorem unaryPorts_injective : Function.Injective unaryPorts := by decide

abbrev unaryFromWork : Cmd 8 41 :=
  .call (ProgramLinking.liftProgram CounterConversions.unaryProgram repeatRegisters unaryPorts)

theorem unaryFromWork_eval (d : Data) (h29 : d.stacks 29 = []) (h30 : d.stacks 30 = []) :
    ∃ n rf, n ≤ CounterConversions.runtimeBound (d.stacks 28) ∧
      Eval unaryFromWork n d
        ⟨rf, Function.update (Function.update d.stacks 28 []) 29
          (List.replicate (CounterPrograms.value (d.stacks 28)) true)⟩ := by
  let small := CounterConversions.state (fun i => d.regs (repeatRegisters i)) (d.stacks 28) []
  obtain ⟨n,hn,hr⟩ := CounterConversions.unary_runs
    (fun i => d.regs (repeatRegisters i)) (d.stacks 28) []
  simp only [List.append_nil] at hr
  let out := CounterConversions.state CounterConversions.zeroRegs []
    (List.replicate (CounterPrograms.value (d.stacks 28)) true)
  have hi : embedState repeatRegisters unaryPorts d small = d := by
    apply embedState_eq _ _ repeatRegisters_injective unaryPorts_injective
    · intro i; rfl
    · intro i
      fin_cases i <;> simp [small,unaryPorts,CounterConversions.state,h29,h30]
    · intros; rfl
    · intros; rfl
  have he := eval_call_lifted CounterConversions.unaryProgram repeatRegisters unaryPorts d
    repeatRegisters_injective unaryPorts_injective hr
  have ho : (embedState repeatRegisters unaryPorts d out).stacks =
      Function.update (Function.update d.stacks 28 []) 29
        (List.replicate (CounterPrograms.value (d.stacks 28)) true) := by
    funext j
    by_cases hj : ∃ i, unaryPorts i = j
    · obtain ⟨i,rfl⟩ := hj
      rw [embedState_stack _ _ _ _ unaryPorts_injective]
      fin_cases i <;> simp [out,unaryPorts,CounterConversions.state,h30]
    · rw [embedState_stack_frame _ _ _ _ j hj]
      have h28 : j ≠ 28 := fun h => hj ⟨0,by simpa [unaryPorts] using h.symm⟩
      have h29' : j ≠ 29 := fun h => hj ⟨1,by simpa [unaryPorts] using h.symm⟩
      simp [h28,h29']
  have hout : embedState repeatRegisters unaryPorts d out =
      ⟨(embedState repeatRegisters unaryPorts d out).regs,
        Function.update (Function.update d.stacks 28 []) 29
          (List.replicate (CounterPrograms.value (d.stacks 28)) true)⟩ := state_ext rfl ho
  refine ⟨n,(embedState repeatRegisters unaryPorts d out).regs,hn,?_⟩
  change Eval unaryFromWork n (embedState repeatRegisters unaryPorts d small)
    (embedState repeatRegisters unaryPorts d out) at he
  rw [hi,hout] at he
  exact he

abbrev unaryFromBinary : Cmd 8 41 :=
  .seq (.call (StackRoutines.copyProgram 31 28 30 (0 : Fin 8) 1)) unaryFromWork

theorem unaryFromBinary_eval (d : Data)
    (h28 : d.stacks 28 = []) (h29 : d.stacks 29 = []) (h30 : d.stacks 30 = []) :
    ∃ n rf, n ≤ 7*(d.stacks 31).length+5+CounterConversions.runtimeBound (d.stacks 31) ∧
      Eval unaryFromBinary n d
        ⟨rf,Function.update d.stacks 29
          (List.replicate (CounterPrograms.value (d.stacks 31)) true)⟩ := by
  let a := afterCopy d 31 28 0 1
  have hc := copy_eval d 31 28 30 0 1 (by decide) (by decide) (by decide) (by decide) h30
  obtain ⟨n,rf,hn,hu⟩ := unaryFromWork_eval a
    (by simp [a,afterCopy,StackRoutines.copyStacks,h29])
    (by simp [a,afterCopy,StackRoutines.copyStacks,h30])
  have ha28 : a.stacks 28 = d.stacks 31 := by simp [a,afterCopy,StackRoutines.copyStacks,h28]
  have hs : Function.update (Function.update a.stacks 28 []) 29
      (List.replicate (CounterPrograms.value (a.stacks 28)) true) =
      Function.update d.stacks 29 (List.replicate (CounterPrograms.value (d.stacks 31)) true) := by
    rw [ha28]
    simp [a,afterCopy,StackRoutines.copyStacks,Function.update_idem,←h28]
  refine ⟨7*(d.stacks 31).length+5+n,rf,?_,?_⟩
  · simpa only [ha28] using Nat.add_le_add_left hn (7*(d.stacks 31).length+5)
  · rw [hs] at hu
    exact hc.seq hu

def logPorts : Fin 3 → Fin 41 := ![39,40,0]

theorem logPorts_injective : Function.Injective logPorts := by decide

abbrev logAt : Cmd 8 41 := .seq resetThree
  (.call (ProgramLinking.liftProgram Log.program repeatRegisters logPorts))

theorem logAt_eval (d : Data) (h40 : d.stacks 40 = []) (h0 : d.stacks 0 = [])
    (ht : 0 < CounterPrograms.value (d.stacks 39)) :
    ∃ word n rf, CounterPrograms.value word = Nat.clog 2 (CounterPrograms.value (d.stacks 39)) ∧
      word.length ≤ (d.stacks 39).length+1 ∧ n ≤ 3+65*((d.stacks 39).length+2)^2 ∧
      Eval logAt n d ⟨rf,Function.update d.stacks 39 word⟩ := by
  obtain ⟨word,hv,hl,n,hn,hr⟩ := Log.program_runs (d.stacks 39) ht
  change Trace Log.program n ((Log.io (d.stacks 39)).withPC (some Log.program.entry))
    ((Log.io word).withPC none) at hr
  let a := resetData d
  let out := Log.io word
  have hi : embedState repeatRegisters logPorts a (Log.io (d.stacks 39)) = a := by
    apply embedState_eq _ _ repeatRegisters_injective logPorts_injective
    · intro i
      fin_cases i <;> simp [a,resetData,repeatRegisters]
    · intro i
      fin_cases i <;> simp [a,resetData,logPorts,h40,h0]
    · intros; rfl
    · intros; rfl
  have he := eval_call_lifted Log.program repeatRegisters logPorts a
    repeatRegisters_injective logPorts_injective hr
  have ho : (embedState repeatRegisters logPorts a out).stacks =
      Function.update d.stacks 39 word := by
    funext j
    by_cases hj : ∃ i, logPorts i = j
    · obtain ⟨i,rfl⟩ := hj
      rw [embedState_stack _ _ _ _ logPorts_injective]
      fin_cases i <;> simp [out,logPorts,h40,h0]
    · rw [embedState_stack_frame _ _ _ _ j hj]
      have h39 : j ≠ 39 := fun h => hj ⟨0,by simpa [logPorts] using h.symm⟩
      simp [a,resetData,h39]
  have hout : embedState repeatRegisters logPorts a out =
      ⟨(embedState repeatRegisters logPorts a out).regs,Function.update d.stacks 39 word⟩ :=
    state_ext rfl ho
  refine ⟨word,3+n,(embedState repeatRegisters logPorts a out).regs,hv,hl,by omega,?_⟩
  change Eval _ n (embedState repeatRegisters logPorts a (Log.io (d.stacks 39)))
    (embedState repeatRegisters logPorts a out) at he
  rw [hi,hout] at he
  exact (resetThree_eval d).seq he

abbrev computeLog : Cmd 8 41 :=
  .seq (.call (StackRoutines.copyProgram 31 39 38 (0 : Fin 8) 1)) logAt

theorem computeLog_eval (d : Data) (h39 : d.stacks 39 = [])
    (h40 : d.stacks 40 = []) (h38 : d.stacks 38 = []) (h0 : d.stacks 0 = [])
    (ht : 0 < CounterPrograms.value (d.stacks 31)) :
    ∃ word n rf, CounterPrograms.value word = Nat.clog 2 (CounterPrograms.value (d.stacks 31)) ∧
      word.length ≤ (d.stacks 31).length+1 ∧
      n ≤ 7*(d.stacks 31).length+8+65*((d.stacks 31).length+2)^2 ∧
      Eval computeLog n d ⟨rf,Function.update d.stacks 39 word⟩ := by
  let a := afterCopy d 31 39 0 1
  have hc := copy_eval d 31 39 38 0 1 (by decide) (by decide) (by decide) (by decide) h38
  have ha39 : a.stacks 39 = d.stacks 31 := by simp [a,afterCopy,StackRoutines.copyStacks,h39]
  obtain ⟨word,n,rf,hv,hl,hn,he⟩ := logAt_eval a
    (by simp [a,afterCopy,StackRoutines.copyStacks,h40])
    (by simp [a,afterCopy,StackRoutines.copyStacks,h0]) (by simpa only [ha39] using ht)
  refine ⟨word,7*(d.stacks 31).length+5+n,rf,by simpa only [ha39] using hv,
    by simpa only [ha39] using hl,?_,?_⟩
  · simp only [ha39] at hn; omega
  · have hs : Function.update a.stacks 39 word = Function.update d.stacks 39 word := by
      simp [a,afterCopy,StackRoutines.copyStacks,Function.update_idem]
    rw [hs] at he
    exact hc.seq he

abbrev metadataFromBinary : Cmd 8 41 :=
  .seq unaryFromBinary (.seq metadataCommand computeLog)

def metadataStacks (stackData : Fin 41 → List Bool) (logword : List Bool) : Fin 41 → List Bool :=
  Function.update (Function.update (Function.update (Function.update stackData
    29 (List.replicate (CounterPrograms.value (stackData 31)) true))
    12 (List.replicate (2*CounterPrograms.value (stackData 31)) true))
    37 (List.replicate (3*CounterPrograms.value (stackData 31)) true)) 39 logword

theorem metadataFromBinary_eval (d : Data)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = []) (h2 : d.stacks 2 = [])
    (h12 : d.stacks 12 = []) (h28 : d.stacks 28 = [])
    (h29 : d.stacks 29 = []) (h30 : d.stacks 30 = [])
    (h37 : d.stacks 37 = []) (h38 : d.stacks 38 = [])
    (h39 : d.stacks 39 = []) (h40 : d.stacks 40 = [])
    (ht : 0 < CounterPrograms.value (d.stacks 31)) :
    ∃ word n rf, CounterPrograms.value word = Nat.clog 2 (CounterPrograms.value (d.stacks 31)) ∧
      word.length ≤ (d.stacks 31).length+1 ∧
      n ≤ 1000*(CounterPrograms.value (d.stacks 31)+(d.stacks 31).length+2)^2 ∧
      Eval metadataFromBinary n d ⟨rf,metadataStacks d.stacks word⟩ := by
  obtain ⟨nu,ru,hnu,hu⟩ := unaryFromBinary_eval d h28 h29 h30
  let a : Data := ⟨ru,Function.update d.stacks 29
    (List.replicate (CounterPrograms.value (d.stacks 31)) true)⟩
  obtain ⟨rm,hm⟩ := metadataCommand_eval a (CounterPrograms.value (d.stacks 31))
    (by simp [a]) (by simp [a,h0]) (by simp [a,h1]) (by simp [a,h2])
    (by simp [a,h12]) (by simp [a,h37])
  let b : Data := ⟨rm,Function.update (Function.update a.stacks
    12 (List.replicate (2*CounterPrograms.value (d.stacks 31)) true))
    37 (List.replicate (3*CounterPrograms.value (d.stacks 31)) true)⟩
  obtain ⟨word,nl,rl,hv,hl,hnl,he⟩ := computeLog_eval b
    (by simp [b,a,h39]) (by simp [b,a,h40]) (by simp [b,a,h38])
    (by simp [b,a,h0]) (by simpa [b,a] using ht)
  have hb31 : b.stacks 31 = d.stacks 31 := by simp [b,a]
  refine ⟨word,nu+(63*CounterPrograms.value (d.stacks 31)+48+nl),rl,
    by simpa only [hb31] using hv,by simpa only [hb31] using hl,?_,?_⟩
  · simp only [hb31] at hnl
    dsimp [CounterConversions.runtimeBound] at hnu
    nlinarith [Nat.zero_le (CounterPrograms.value (d.stacks 31)*(d.stacks 31).length)]
  · exact hu.seq (hm.seq he)

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms

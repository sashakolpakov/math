import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramField
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramRepeat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramWords

namespace OAI.Algorithms

/-! Native production of the ternary modulus from runtime binary precision.
The output bytes themselves instantiate the prepared-modulus structure;
no canonical encoding or precomputed power is supplied to the machine. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpScanPrimitives

def modulusPorts : Fin 22 → Fin 41 :=
  ![0,31,5,1,2,3,4,6,7,8,9,10,11,13,14,15,16,18,19,20,21,22]

theorem modulusPorts_injective : Function.Injective modulusPorts := by decide

abbrev modulusCommand : Cmd 8 41 :=
  .call (ProgramLinking.liftProgram LeafParametersProgram.Field.program id modulusPorts)

def ModulusWorkspaceEmpty (d : Data) : Prop :=
  ∀ i : Fin 22, i ≠ 1 → d.stacks (modulusPorts i) = []

theorem modulusCommand_eval (d : Data) (ready : ModulusWorkspaceEmpty d) :
    ∃ (M : SubexpPreparedQuartic.Modulus 3 (BinaryArithmetic.toNat (d.stacks 31))), ∃ n rf,
      n ≤ 1001*(BinaryArithmetic.toNat (d.stacks 31)+(d.stacks 31).length+2)^2 ∧
      Eval modulusCommand n d ⟨rf,Function.update d.stacks 5 M.bits⟩ := by
  let words : SubexpBlockParameterProgram.Words := fun i =>
    if i = 1 then d.stacks 31 else []
  obtain ⟨n,rf,word,he,hv,hl,hn⟩ := LeafParametersProgram.Field.command_eval d.regs words
    (by simp [words]) (by simp [words])
  have hval : BinaryArithmetic.toNat word = 3 ^ BinaryArithmetic.toNat (d.stacks 31) := by
    simpa [words] using hv
  have hwidth : word.length ≤ SubexpLiftRing.baseWidth 3
      (BinaryArithmetic.toNat (d.stacks 31)) + 1 := by
    have ht : Nat.log 2 3 = 1 := (Nat.log_eq_one_iff').2 (by decide)
    simpa [words,SubexpLiftRing.baseWidth,ht,Nat.mul_comm,Nat.add_comm] using hl
  let M : SubexpPreparedQuartic.Modulus 3 (BinaryArithmetic.toNat (d.stacks 31)) :=
    ⟨word,hwidth,hval⟩
  let a := SubexpBlockParameterProgram.state d.regs words
  let b := SubexpBlockParameterProgram.state rf (Function.update words 2 word)
  have hproj : ∀ i, d.stacks (modulusPorts i) = a.stacks i := by
    intro i
    by_cases hi : i = 1
    · subst i
      simp [a,SubexpBlockParameterProgram.state,words,modulusPorts]
    · have hr := ready i hi
      fin_cases i <;> norm_num [a,SubexpBlockParameterProgram.state,words,
        modulusPorts,Function.update,Fin.ext_iff] at * <;> assumption
  have hstate : b.stacks = Function.update a.stacks 2 word := by
    have h := congrArg (fun q : StructuredProgram.State 8 22 => q.stacks)
      (SubexpBlockParameterProgram.state_update d.regs rf words 2 word)
    exact h.symm
  have hi : embedState id modulusPorts d a = d := by
    apply embedState_eq _ _ Function.injective_id modulusPorts_injective
    · intro i; rfl
    · exact hproj
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intros; rfl
  have hout : (embedState id modulusPorts d b).stacks = Function.update d.stacks 5 word := by
    funext j
    by_cases hj : ∃ i, modulusPorts i = j
    · obtain ⟨i,rfl⟩ := hj
      rw [embedState_stack _ _ _ _ modulusPorts_injective,hstate]
      by_cases hi : i = 2
      · subst i; simp [modulusPorts]
      · have htarget : modulusPorts i ≠ 5 := by
          intro h
          fin_cases i <;> simp [modulusPorts] at h hi
        rw [Function.update_of_ne hi,Function.update_of_ne htarget]
        exact (hproj i).symm
    · rw [embedState_stack_frame _ _ _ _ j hj]
      have hj5 : j ≠ 5 := fun h => hj ⟨2,by simpa [modulusPorts] using h.symm⟩
      simp [hj5]
  have run := eval_call_lifted LeafParametersProgram.Field.program id modulusPorts d
    Function.injective_id modulusPorts_injective (compiled_halt_trace he 1 2)
  have hb : embedState id modulusPorts d b =
      ⟨(embedState id modulusPorts d b).regs,Function.update d.stacks 5 word⟩ := state_ext rfl hout
  change Eval modulusCommand (n+1) (embedState id modulusPorts d a)
    (embedState id modulusPorts d b) at run
  rw [hi,hb] at run
  refine ⟨M,n+1,_,?_,run⟩
  have hp := LeafParametersProgram.Field.bound_polynomial (d.stacks 31)
  simp only [words,ite_true] at hn
  have hpos : 0 < (BinaryArithmetic.toNat (d.stacks 31)+(d.stacks 31).length+2)^2 := by
    positivity
  omega

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms

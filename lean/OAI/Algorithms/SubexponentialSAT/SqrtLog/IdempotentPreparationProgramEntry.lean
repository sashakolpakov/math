import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramMetadata
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

namespace OAI.Algorithms

/-! A table entry is selected by a fixed unary bit program and copied from
one of six scalar cache words. The table itself is constructed at runtime. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open IdempotentTableEntryProgram (codeBits outputPort entryCode)

def entrySource (c : Fin 6) : Fin 41 := ![17,18,20,19,21,23] c

abbrev entryCopy (source : Fin 41) : Cmd 8 41 :=
  .call (StackRoutines.copyProgram source 22 4 (0 : Fin 8) 1)

abbrev dispatchEntry : Cmd 8 41 :=
  .ite 7 (.ite 5 (entryCopy 23) (entryCopy 21))
    (.ite 6 (.ite 5 (entryCopy 19) (entryCopy 20))
      (.ite 5 (entryCopy 18) (entryCopy 17)))

theorem dispatchEntry_eval (d : Data) (c : Fin 6) (h4 : d.stacks 4 = [])
    (hcode : ∀ z, d.regs (outputPort z) = codeBits c z) :
    ∃ n rf, n ≤ 7*(d.stacks (entrySource c)).length+8 ∧
      Eval dispatchEntry n d ⟨rf,Function.update d.stacks 22
        (d.stacks (entrySource c) ++ d.stacks 22)⟩ := by
  have hcopy := copy_eval d (entrySource c) 22 4 0 1
    (by fin_cases c <;> decide) (by fin_cases c <;> decide)
    (by decide) (by decide) h4
  have h0 := hcode 0
  have h1 := hcode 1
  have h2 := hcode 2
  fin_cases c <;> norm_num [outputPort,codeBits] at h0 h1 h2 <;>
    simp only [entrySource] at hcopy ⊢
  all_goals first
    | refine ⟨_,_,?_,Eval.ite_false (test := 7) h2 (Eval.ite_false (test := 6) h1 (Eval.ite_false (test := 5) h0 hcopy))⟩
    | refine ⟨_,_,?_,Eval.ite_false (test := 7) h2 (Eval.ite_false (test := 6) h1 (Eval.ite_true (test := 5) h0 hcopy))⟩
    | refine ⟨_,_,?_,Eval.ite_false (test := 7) h2 (Eval.ite_true (test := 6) h1 (Eval.ite_false (test := 5) h0 hcopy))⟩
    | refine ⟨_,_,?_,Eval.ite_false (test := 7) h2 (Eval.ite_true (test := 6) h1 (Eval.ite_true (test := 5) h0 hcopy))⟩
    | refine ⟨_,_,?_,Eval.ite_true (test := 7) h2 (Eval.ite_false (test := 5) h0 hcopy)⟩
    | refine ⟨_,_,?_,Eval.ite_true (test := 7) h2 (Eval.ite_true (test := 5) h0 hcopy)⟩
  all_goals omega

def selectorPorts : Fin 4 → Fin 41 := Fin.castAdd 37

theorem selectorPorts_injective : Function.Injective selectorPorts := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 41 => x.val) h)

abbrev selector : Cmd 8 41 :=
  .call (ProgramLinking.liftProgram IdempotentTableEntryProgram.program id selectorPorts)

theorem selector_eval (d : Data) (i j k : ℕ)
    (h0 : d.stacks 0 = List.replicate i true)
    (h1 : d.stacks 1 = List.replicate j true)
    (h2 : d.stacks 2 = List.replicate k true) (h3 : d.stacks 3 = []) :
    ∃ n rf zs bs, n ≤ 40*(i+j+k+1) ∧ zs.length+bs.length ≤ i+j+k ∧
      Eval selector n d
        ⟨rf,Function.update (Function.update (Function.update (Function.update d.stacks
          0 []) 1 []) 2 zs) 3 bs⟩ ∧
      (∀ z, rf (outputPort z) = codeBits (entryCode i j k) z) := by
  obtain ⟨n,rf,zs,bs,hn,hr,hcode,hsize⟩ :=
    IdempotentTableEntryProgram.program_trace i j k d.regs
  let a := IdempotentTableEntryProgram.data d.regs (List.replicate i true)
    (List.replicate j true) (List.replicate k true) []
  let b := IdempotentTableEntryProgram.data rf [] [] zs bs
  have hi : embedState id selectorPorts d a = d := by
    apply embedState_eq _ _ Function.injective_id selectorPorts_injective
    · intro z; rfl
    · intro z; fin_cases z <;> simp [a,IdempotentTableEntryProgram.data,selectorPorts,h0,h1,h2,h3]
    · intro z hz; exact False.elim (hz ⟨z,rfl⟩)
    · intros; rfl
  have hs : (embedState id selectorPorts d b).stacks =
      Function.update (Function.update (Function.update (Function.update d.stacks
        0 []) 1 []) 2 zs) 3 bs := by
    funext z
    by_cases hz : ∃ x, selectorPorts x = z
    · obtain ⟨x,rfl⟩ := hz
      rw [embedState_stack _ _ _ _ selectorPorts_injective]
      fin_cases x <;> simp [b,IdempotentTableEntryProgram.data,selectorPorts]
    · rw [embedState_stack_frame _ _ _ _ z hz]
      have hzero : z ≠ 0 := fun h => hz ⟨0,by simpa [selectorPorts] using h.symm⟩
      have hone : z ≠ 1 := fun h => hz ⟨1,by simpa [selectorPorts] using h.symm⟩
      have htwo : z ≠ 2 := fun h => hz ⟨2,by simpa [selectorPorts] using h.symm⟩
      have hthree : z ≠ 3 := fun h => hz ⟨3,by simpa [selectorPorts] using h.symm⟩
      simp [hzero,hone,htwo,hthree]
  have hb : embedState id selectorPorts d b =
      ⟨rf,Function.update (Function.update (Function.update (Function.update d.stacks
        0 []) 1 []) 2 zs) 3 bs⟩ := by
    apply state_ext
    · funext z
      exact embedState_register _ _ _ _ Function.injective_id z
    · exact hs
  have he := eval_call_lifted IdempotentTableEntryProgram.program id selectorPorts d
    Function.injective_id selectorPorts_injective hr
  refine ⟨n,rf,zs,bs,hn,hsize,?_,hcode⟩
  change Eval selector n (embedState id selectorPorts d a) (embedState id selectorPorts d b) at he
  simpa only [hi,hb] using he

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyBasic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramZipSemantics

namespace OAI.Algorithms

/-! Relocation of the concrete stream merger into the sequential controller ABI. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def mergeRegisters (i : Fin 8) : Fin 16 := i.castAdd 8
def mergePorts : Fin 14 → Fin 48 := ![0,12,1,2,3,4,5,6,7,13,14,17,15,16]
theorem mergeRegisters_injective : Function.Injective mergeRegisters := Fin.castAdd_injective _ _
theorem mergePorts_injective : Function.Injective mergePorts := by decide

abbrev merge : Cmd 16 48 := liftCommand Zip.command 0 8 mergeRegisters mergePorts

def MergeInput (wi wh : List Bool) (ps : List (ℕ × ℕ)) (d : Data) : Prop :=
  ∀ i, d.stacks (mergePorts i) = (Zip.input (d.regs ∘ mergeRegisters) wi wh ps).stacks i

theorem merge_projection (wi wh : List Bool) (ps : List (ℕ × ℕ))
    (d : Data) (h : MergeInput wi wh ps d) :
    projectState mergeRegisters mergePorts d = Zip.input (d.regs ∘ mergeRegisters) wi wh ps := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · exact (Zip.input_regs _ _ _ _).symm
  · exact funext h

theorem merge_eval (wi wh : List Bool) (ps : List (ℕ × ℕ)) (d : Data)
    (h : MergeInput wi wh ps d) :
    ∃ t ≤ Zip.budget wi wh ps+1, ∃ e : Data,
      Eval merge t d e ∧
      e.stacks 7 = ProgramEncoding.encodeRecords (Streams.scores wi wh ps) ∧
      e.stacks 0=[] ∧ e.stacks 12=[] ∧
      (∀ j, j ≠ 0 → j ≠ 7 → j ≠ 12 → e.stacks j=d.stacks j) := by
  obtain ⟨t,ht,b,hb,ho,hi,hh,hf⟩ := Zip.command_eval (d.regs ∘ mergeRegisters) wi wh ps
  have hb' : Eval Zip.command t (projectState mergeRegisters mergePorts d) b := by
    rw [merge_projection wi wh ps d h]
    exact hb
  let e := embedState mergeRegisters mergePorts d b
  have he := eval_liftCommand_from_state Zip.command 0 8 mergeRegisters mergePorts d
    mergeRegisters_injective mergePorts_injective hb'
  have hs (i : Fin 14) : e.stacks (mergePorts i)=b.stacks i :=
    embedState_stack mergeRegisters mergePorts d b mergePorts_injective i
  refine ⟨t+1,Nat.add_le_add_right ht 1,e,he,(hs 8).trans ho,
    (hs 0).trans (hf 0 (by decide) (by decide) (by decide)),
    (hs 1).trans (hf 1 (by decide) (by decide) (by decide)),?_⟩
  intro j hj0 hj7 hj12
  by_cases hm : ∃ i,mergePorts i=j
  · obtain ⟨i,rfl⟩ := hm
    rw [hs,h i,Zip.input_stacks]
    fin_cases i <;> first
      | exact False.elim (hj0 rfl)
      | exact False.elim (hj7 rfl)
      | exact False.elim (hj12 rfl)
      | exact hi
      | exact hh
      | exact hf _ (by decide) (by decide) (by decide)
  · exact embedState_stack_frame mergeRegisters mergePorts d b j hm

abbrev finishMerged : Cmd 16 48 := move 7 0 1

theorem finishMerged_eval (wi wh : List Bool) (ps : List (ℕ × ℕ)) (d : Data)
    (h : MergeInput wi wh ps d) :
    ∃ t ≤ Zip.budget wi wh ps+1+
        6*(ProgramEncoding.encodeRecords (Streams.scores wi wh ps)).length+6,
      ∃ e : Data, Eval (.seq merge finishMerged) t d e ∧
      e.stacks 0=ProgramEncoding.encodeRecords (Streams.scores wi wh ps) ∧
      e.stacks 12=[] ∧
      (∀ j, j ≠ 0 → j ≠ 12 → e.stacks j=d.stacks j) := by
  obtain ⟨t,ht,b,hb,ho,h0,h12,hf⟩ := merge_eval wi wh ps d h
  have hd1 : d.stacks 1=[] := by
    have hh := h 2
    simpa [mergePorts,Zip.input_stacks] using hh
  have hd7 : d.stacks 7=[] := by
    have hh := h 8
    simpa [mergePorts,Zip.input_stacks] using hh
  have hb1 : b.stacks 1=[] := (hf 1 (by decide) (by decide) (by decide)).trans hd1
  have hm := move_eval b 7 0 1 (by decide) (by decide) (by decide) h0 hb1
  refine ⟨t+(6*(b.stacks 7).length+6),?_,moved b 7 0,hb.seq hm,?_,?_,?_⟩
  · rw [ho]
    omega
  · simpa [moved] using ho
  · simpa [moved] using h12
  · intro j hj0 hj12
    by_cases hj7 : j=7
    · subst j
      simp [moved,hd7]
    · simpa [moved,hj0,hj7] using hf j hj0 hj7 hj12

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms

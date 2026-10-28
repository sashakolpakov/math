import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgramNative
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Concrete storage and framed service calls for each head assignment. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafAssignmentSetupProgram
open SubexponentialSAT BitProgram StructuredCalls StackRoutines

abbrev Data := State 40 768
abbrev Code := Cmd 40 768

def transfer (src dst : Fin 768) : Code :=
  .call (transferProgram src dst (0 : Fin 40) 1)
def transferred (a : Data) (src dst : Fin 768) : Data :=
  ⟨readRegs a.regs 0 1 none, transferStacks src dst a.stacks⟩
theorem transfer_eval (a : Data) (src dst : Fin 768) (h : src ≠ dst) :
    Eval (transfer src dst) (3*(a.stacks src).length+3) a (transferred a src dst) := by
  apply Eval.call
  have he := halt_after_trace _
    (transferProgram_trace src dst (0 : Fin 40) 1 h (by decide) a.regs a.stacks) 3 rfl rfl
  simpa [transferred,transferResult,StructuredProgram.State.withPC,transferProgram,
    Nat.add_assoc] using he

def move (src dst : Fin 768) : Code := .seq (transfer src 359) (transfer 359 dst)
def moved (a : Data) (src dst : Fin 768) : Data :=
  ⟨readRegs (readRegs a.regs 0 1 none) 0 1 none,
    Function.update (Function.update a.stacks src []) dst (a.stacks src)⟩
theorem move_eval (a : Data) (src dst : Fin 768)
    (hs : src ≠ 359) (hd : dst ≠ 359) (hsd : src ≠ dst)
    (ht : a.stacks 359 = []) (he : a.stacks dst = []) :
    Eval (move src dst) (6*(a.stacks src).length+6) a (moved a src dst) := by
  have h1 := transfer_eval a src 359 hs
  have h2 := transfer_eval (transferred a src 359) 359 dst hd.symm
  have hlen : ((transferred a src 359).stacks 359).length = (a.stacks src).length := by
    simp [transferred,transferStacks,ht]
  have hfinal : transferred (transferred a src 359) 359 dst = moved a src dst := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hsrc : i=src
      · subst i; simp [transferred,transferStacks,ht,he,hs,hd,hsd,Ne.symm hsd]
      by_cases hdst : i=dst
      · subst i; simp [transferred,transferStacks,ht,he,hd,Ne.symm hsd]
      by_cases htmp : i=359
      · subst i; simp [transferred,transferStacks,ht,he,hd,Ne.symm hs,Ne.symm hd,Ne.symm hsd]
      simp [transferred,transferStacks,ht,he,hd,hsrc,hdst,htmp,Ne.symm hsd]
  rw [hlen,hfinal] at h2
  have hx := h1.seq h2
  change Eval (move src dst) _ a (moved a src dst) at hx
  convert hx using 1 ; omega

def clear (src : Fin 768) : Code := .call (clearProgram src (0 : Fin 40) 1)
def cleared (a : Data) (src : Fin 768) : Data :=
  ⟨readRegs a.regs 0 1 none, Function.update a.stacks src []⟩
theorem clear_eval (a : Data) (src : Fin 768) :
    Eval (clear src) (2*(a.stacks src).length+3) a (cleared a src) := by
  apply Eval.call
  have he := halt_after_trace _
    (clearProgram_trace src (0 : Fin 40) 1 a.regs a.stacks) 2 rfl rfl
  simpa [cleared,clearResult,clearStacks,StructuredProgram.State.withPC,clearProgram,
    Nat.add_assoc] using he

def register (i : Fin 8) : Fin 40 := i.castAdd 32
theorem register_injective : Function.Injective register := Fin.castAdd_injective 8 32

def mergePorts : Fin 10 → Fin 768 := ![174,178,177,190,207,340,341,342,343,145]
def weightPorts : Fin 10 → Fin 768 := ![174,168,178,190,207,340,341,342,343,148]
theorem mergePorts_injective : Function.Injective mergePorts := by decide
theorem weightPorts_injective : Function.Injective weightPorts := by decide

def serviceResult (a : Data) (ports : Fin 10 → Fin 768)
    (rf : Fin 8 → Bool) (word : List Bool) : Data :=
  { embedState register ports a ⟨rf,a.stacks ∘ ports⟩ with
    «stacks» := Function.update a.stacks (ports 9) word }

theorem serviceResult_eq (a : Data) (ports : Fin 10 → Fin 768)
    (hp : Function.Injective ports) (rf : Fin 8 → Bool) (word : List Bool) :
    embedState register ports a ⟨rf,Function.update (a.stacks ∘ ports) 9 word⟩ =
      serviceResult a ports rf word := by
  rw [embedState_update_stack register ports a (⟨rf,a.stacks ∘ ports⟩ : State 8 10) hp 9 word]
  have hs : (embedState register ports a ⟨rf,a.stacks ∘ ports⟩).stacks = a.stacks := by
    funext i
    by_cases h : ∃j,ports j=i
    · obtain ⟨j,rfl⟩ := h
      exact embedState_stack register ports a _ hp j
    · exact embedState_stack_frame register ports a _ i h
  simp only [serviceResult,hs]

def mergeCommand : Code :=
  .call (ProgramLinking.liftProgram LeafAssignmentMergeProgram.Native.program register mergePorts)
def weightCommand : Code :=
  .call (ProgramLinking.liftProgram LeafWeightProgram.Native.program register weightPorts)
def scratch : List (Fin 768) := [340,341,342,343]

theorem merge_eval (a : Data)
    (hempty : ∀i∈scratch,a.stacks i=[])
    (hout : a.stacks 145=[])
    (hh : (a.stacks 174).length=(a.stacks 178).length)
    (hb : (a.stacks 174).length=(a.stacks 177).length) :
    ∃rf, Eval mergeCommand (30*(a.stacks 174).length+22) a
      (serviceResult a mergePorts rf
        (LeafAssignmentMergeProgram.merge (a.stacks 174) (a.stacks 178) (a.stacks 177))) := by
  have hp : projectState register mergePorts a =
      LeafWeightProgram.Native.data (a.regs ∘ register) (a.stacks 174) (a.stacks 178)
        (a.stacks 177) (a.stacks 190) (a.stacks 207) [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;>
        simp [mergePorts,LeafWeightProgram.Native.tapes,
          hempty 340 (by simp [scratch]),hempty 341 (by simp [scratch]),
          hempty 342 (by simp [scratch]),hempty 343 (by simp [scratch]),hout]
  obtain ⟨rf,h⟩ := LeafAssignmentMergeProgram.Native.program_trace (a.regs ∘ register)
    (a.stacks 174) (a.stacks 178) (a.stacks 177) (a.stacks 190) (a.stacks 207) hh hb
  have he := eval_call_from_state LeafAssignmentMergeProgram.Native.program register mergePorts a
    register_injective mergePorts_injective (by rw [hp]; exact h)
  refine ⟨rf,?_⟩
  have ho : LeafWeightProgram.Native.data rf (a.stacks 174) (a.stacks 178)
      (a.stacks 177) (a.stacks 190) (a.stacks 207) [] [] []
      (LeafAssignmentMergeProgram.merge (a.stacks 174) (a.stacks 178) (a.stacks 177)) =
      (⟨rf,Function.update (a.stacks ∘ mergePorts) 9
        (LeafAssignmentMergeProgram.merge (a.stacks 174) (a.stacks 178) (a.stacks 177))⟩ : State 8 10) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i; fin_cases i <;>
      simp [mergePorts,LeafWeightProgram.Native.tapes,
        hempty 340 (by simp [scratch]),hempty 341 (by simp [scratch]),
        hempty 342 (by simp [scratch]),hempty 343 (by simp [scratch])]
  simp only [LeafAssignmentMergeProgram.Native.data] at he
  rw [ho,serviceResult_eq a mergePorts mergePorts_injective] at he
  exact he

theorem weight_eval (a : Data)
    (hempty : ∀i∈scratch,a.stacks i=[])
    (hout : a.stacks 148=[])
    (hs : (a.stacks 174).length=(a.stacks 168).length)
    (hh : (a.stacks 174).length=(a.stacks 178).length) :
    ∃rf, Eval weightCommand
      (29*(a.stacks 174).length+7*(LeafWeightProgram.Native.result (a.stacks 174)
        (a.stacks 168) (a.stacks 178) (a.stacks 190) (a.stacks 207)).length+26) a
      (serviceResult a weightPorts rf (LeafWeightProgram.Native.result (a.stacks 174)
        (a.stacks 168) (a.stacks 178) (a.stacks 190) (a.stacks 207))) := by
  have hp : projectState register weightPorts a =
      LeafWeightProgram.Native.data (a.regs ∘ register) (a.stacks 174) (a.stacks 168)
        (a.stacks 178) (a.stacks 190) (a.stacks 207) [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;>
        simp [weightPorts,LeafWeightProgram.Native.tapes,
          hempty 340 (by simp [scratch]),hempty 341 (by simp [scratch]),
          hempty 342 (by simp [scratch]),hempty 343 (by simp [scratch]),hout]
  obtain ⟨rf,h⟩ := LeafWeightProgram.Native.program_trace (a.regs ∘ register)
    (a.stacks 174) (a.stacks 168) (a.stacks 178) (a.stacks 190) (a.stacks 207) hs hh
  have he := eval_call_from_state LeafWeightProgram.Native.program register weightPorts a
    register_injective weightPorts_injective (by rw [hp]; exact h)
  refine ⟨rf,?_⟩
  have ho : LeafWeightProgram.Native.data rf (a.stacks 174) (a.stacks 168)
      (a.stacks 178) (a.stacks 190) (a.stacks 207) [] [] []
      (LeafWeightProgram.Native.result (a.stacks 174) (a.stacks 168) (a.stacks 178)
        (a.stacks 190) (a.stacks 207)) =
      (⟨rf,Function.update (a.stacks ∘ weightPorts) 9
        (LeafWeightProgram.Native.result (a.stacks 174) (a.stacks 168) (a.stacks 178)
          (a.stacks 190) (a.stacks 207))⟩ : State 8 10) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i; fin_cases i <;>
      simp [weightPorts,LeafWeightProgram.Native.tapes,
        hempty 340 (by simp [scratch]),hempty 341 (by simp [scratch]),
        hempty 342 (by simp [scratch]),hempty 343 (by simp [scratch])]
  rw [ho,serviceResult_eq a weightPorts weightPorts_injective] at he
  exact he

end SubexponentialSAT.SqrtLog.LeafAssignmentSetupProgram
end

end OAI.Algorithms

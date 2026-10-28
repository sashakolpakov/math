import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoot
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramRetain
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramHead

namespace OAI.Algorithms

/-! Fixed physical per-node head setup. Each head is selected from the actual
word table; its complete all-incidence matrix is built and bucketed; the
actual attained buckets are appended to the Cartesian stream. The entry
command is the sole explicit service parameter and must be instantiated by
the concrete LayoutProgram integer entry before claiming a closed solver. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

def privatePorts : List (Fin 768) := List.ofFn (fun i : Fin 40 => ⟨640+i.val,by omega⟩)
def cleanupPorts : List (Fin 768) := workPorts (s:=288) (by decide) ++ privatePorts
def cleanup : Code := clearMany cleanupPorts

def initializeNode : Code := .seq boot (.seq retainCache tupleInit)

abbrev command (entry : Cmd 16 256) : Code :=
  .seq initializeNode (.seq (headLoop entry) (.seq finalize cleanup))

abbrev program (entry : Cmd 16 256) := compiled (command entry) 307 163

def wideRegisters : Fin 16 → Fin 40 := Fin.castAdd 24
abbrev wideProgram (entry : Cmd 16 256) :=
  ProgramLinking.liftProgram (program entry) wideRegisters id

theorem privatePorts_mem (i : Fin 768) : i∈privatePorts ↔ 640 ≤ i.val ∧ i.val < 680 := by
  simp only [privatePorts,List.mem_ofFn]
  constructor
  · rintro ⟨j,hj⟩
    have := congrArg Fin.val hj
    have := j.isLt
    simp only at *
    omega
  · intro h
    refine ⟨⟨i.val-640,by omega⟩,?_⟩
    apply Fin.ext
    simp
    omega

theorem cleanup_eval (a : Data) : Eval cleanup (clearManyCost cleanupPorts a) a
    (clearManyState cleanupPorts a) := clearMany_eval _ _

theorem cleanup_private (a : Data) (i : Fin 768) (hi : 640 ≤ i.val ∧ i.val < 680) :
    (clearManyState cleanupPorts a).stacks i=[] := by
  rw [clearMany_stacks,ite_eq_left]
  exact List.mem_append_right _ ((privatePorts_mem i).mpr hi)

theorem cleanup_work (a : Data) (i : Fin 288) :
    (clearManyState cleanupPorts a).stacks (workPort (by decide) i)=[] := by
  rw [clearMany_stacks,ite_eq_left]
  exact List.mem_append_left _ (work_mem_workPorts (by decide) i)

theorem cleanup_frame (a : Data) (i : Fin 768)
    (hi : (i.val < 340 ∨ 628 ≤ i.val) ∧ (i.val < 640 ∨ 680 ≤ i.val)) :
    (clearManyState cleanupPorts a).stacks i=a.stacks i := by
  rw [clearMany_stacks,ite_eq_right]
  simp only [cleanupPorts,List.mem_append,not_or]
  constructor
  · simp only [workPorts,List.mem_ofFn,not_exists]
    intro j hj
    have h := congrArg Fin.val hj
    have := j.isLt
    simp only [workPort] at h
    omega
  · rw [privatePorts_mem]
    omega

/-- Any completed execution of the concrete local program embeds into the
40-register leaf worker while preserving all registers16..39. -/
theorem wide_execution (entry : Cmd 16 256) (a : State 40 768) (b : Data) {n : ℕ}
    (he : Trace (program entry) n
      ((projectState wideRegisters id a).withPC (some (program entry).entry)) (b.withPC none)) :
    Eval (.call (wideProgram entry)) n a (embedState wideRegisters id a b) ∧
      (∀ i : Fin 40,16 ≤ i.val→(embedState wideRegisters id a b).regs i=a.regs i) := by
  refine ⟨eval_call_from_state (program entry) wideRegisters id a
    (Fin.castAdd_injective _ _) Function.injective_id he,?_⟩
  intro i hi
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have := congrArg Fin.val hj
  have := j.isLt
  simp only [wideRegisters,Fin.val_castAdd] at *
  omega

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end OAI.Algorithms

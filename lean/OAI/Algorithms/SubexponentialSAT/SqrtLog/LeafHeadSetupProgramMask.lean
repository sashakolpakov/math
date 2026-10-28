import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeWide

namespace OAI.Algorithms

/-! The indexed collector owns seven arbitrarily long tapes. They are not
inputs to the head builder. Clearing them for a resource proof preserves
every physical input condition; replay restores their original contents. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Footprint
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls ProgramTapeReplay

def carriedPorts : List (Fin 768) := [256,265,301,302,303,304,305]
def Hidden (i : Fin 768) : Prop := i ∈ carriedPorts
instance : DecidablePred Hidden := fun _ => inferInstanceAs (Decidable (_ ∈ carriedPorts))

def mask {r : ℕ} (a : State r 768) : State r 768 :=
  rebaseState Hidden (fun _ => []) a

def restore {r : ℕ} (a b : State r 768) : State r 768 :=
  rebaseState Hidden a.stacks b

def LocalWordBound {r : ℕ} (B : ℕ) (a : State r 768) : Prop :=
  ∀ i, i ∉ carriedPorts → (a.stacks i).length ≤ B

@[simp] theorem mask_regs {r : ℕ} (a : State r 768) : (mask a).regs=a.regs := rfl
@[simp] theorem restore_regs {r : ℕ} (a b : State r 768) :
    (restore a b).regs=b.regs := rfl

theorem mask_stack {r : ℕ} (a : State r 768) (i : Fin 768) (hi : ¬ Hidden i) :
    (mask a).stacks i=a.stacks i := ite_eq_right hi
theorem restore_stack {r : ℕ} (a b : State r 768) (i : Fin 768) (hi : ¬ Hidden i) :
    (restore a b).stacks i=b.stacks i := ite_eq_right hi
theorem restore_hidden {r : ℕ} (a b : State r 768) (i : Fin 768) (hi : Hidden i) :
    (restore a b).stacks i=a.stacks i := ite_eq_left hi

@[simp] theorem restore_mask {r : ℕ} (a : State r 768) : restore a (mask a)=a := by
  apply congrArg (StructuredProgram.State.mk a.regs)
  funext i
  by_cases hi : Hidden i <;> simp [mask,rebaseState,rebaseStacks,hi]

theorem mask_wordBound {r : ℕ} (a : State r 768) (B : ℕ) (ha : LocalWordBound B a) :
    ∀ i,((mask a).stacks i).length ≤ B := by
  intro i
  by_cases hi : Hidden i
  · simp [mask,rebaseState,rebaseStacks,hi]
  · rw [mask_stack a i hi]
    exact ha i hi

theorem project_mask (a : State 40 768) : Native.project (mask a)=mask (Native.project a) := rfl

theorem mask_ready (s : Native.Inputs) (a : Data) (ha : Native.Ready s a) :
    Native.Ready s (mask a) := by
  constructor
  all_goals first
    | simpa only [mask_stack _ _ (by decide : ¬ Hidden 128)] using ha.ambient
    | simpa only [mask_stack _ _ (by decide : ¬ Hidden 129)] using ha.factors
    | simpa only [mask_stack _ _ (by decide : ¬ Hidden 130)] using ha.colors
    | simpa only [mask_stack _ _ (by decide : ¬ Hidden 131)] using ha.nodes
    | simpa only [mask_stack _ _ (by decide : ¬ Hidden 132)] using ha.wordWidth
    | simpa only [mask_stack _ _ (by decide : ¬ Hidden 133)] using ha.words
    | simpa only [mask_stack _ _ (by decide : ¬ Hidden 134)] using ha.low
    | simpa only [mask_stack _ _ (by decide : ¬ Hidden 135)] using ha.metadata
    | simpa only [mask_stack _ _ (by decide : ¬ Hidden 136)] using ha.plans
    | simpa only [mask_stack _ _ (by decide : ¬ Hidden 138)] using ha.order
    | simpa only [mask_stack _ _ (by decide : ¬ Hidden 139)] using ha.height
    | simpa only [mask_stack _ _ (by decide : ¬ Hidden 140)] using ha.width
    | simpa only [mask_stack _ _ (by decide : ¬ Hidden 141)] using ha.offset
    | simpa only [mask_stack _ _ (by decide : ¬ Hidden 307)] using ha.node
    | simpa only [mask_stack _ _ (by decide : ¬ Hidden 660)] using ha.tuples
    | simpa only [mask_stack _ _ (by decide : ¬ Hidden 665)] using ha.marker

theorem wide_mask_ready (s : Native.Inputs) (a : State 40 768)
    (ha : Native.Ready s (Native.project a)) : Native.Ready s (Native.project (mask a)) :=
  mask_ready s (Native.project a) ha

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Footprint

end

end OAI.Algorithms

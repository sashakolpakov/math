import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyNativeFactor

namespace OAI.Algorithms

/-! The selected-factor incidence service with a concrete source generator.
All ring/layout inputs are copied from persistent masters, and the complete
private worker is reclaimed after exporting the actual lookup table. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Incidence
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
abbrev Data := State 16 768

def pairs : List (Fin 768 × Fin 768) :=
  [(194,345),(202,350),(280,444),
   (194,534),(201,541),(202,542),(203,543),(204,544),
   (145,546),(280,547),(207,548),(78,549),(280,551),(128,552),
   (243,553),(702,574),(703,575),(243,583)]

abbrev stage : Cmd 16 768 := .seq (copyMany 684 pairs) SourceControls.cutoff
def staged (a : Data) : Data := SourceControls.cutoffState (copyManyState pairs a)
def stageCost (a : Data) : ℕ := copyManyCost pairs a + 7*(a.stacks 138).length+7

abbrev service : Cmd 16 768 := PerturbationAssembly.prepareFactor Source.command

def workerPorts : List (Fin 768) :=
  (List.finRange 340).map (fun i => (⟨340+i.val,by omega⟩ : Fin 768))
abbrev exportResult : Cmd 16 768 := .seq (copyCmd 561 62 684) (clearMany workerPorts)
def exported (a : Data) : Data := clearManyState workerPorts (copyState 561 62 a)
def exportCost (a : Data) : ℕ := 7*(a.stacks 561).length+5+
  clearManyCost workerPorts (copyState 561 62 a)

abbrev command : Cmd 16 768 := .seq stage (.seq service exportResult)
def program := compiled command 556 62

def callerRegisters (i : Fin 16) : Fin 40 := i.castAdd 24
abbrev caller : Cmd 40 768 := .call (ProgramLinking.liftProgram program callerRegisters id)

theorem pairs_valid : ∀ p ∈ pairs, p.1 ≠ p.2 ∧ p.1 ≠ 684 ∧ (684 : Fin 768) ≠ p.2 := by
  intro p hp
  simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide

theorem stage_eval (a : Data) (htmp : a.stacks 684 = []) :
    Eval stage (stageCost a) a (staged a) := by
  have htmp' : (copyManyState pairs a).stacks 684 = [] := by
    rw [copyMany_frame _ _ _ (fun p hp => (pairs_valid p hp).2.2)]
    exact htmp
  have hR : (copyManyState pairs a).stacks 138 = a.stacks 138 := by
    apply copyMany_frame
    intro p hp
    simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide
  have h := (copyMany_eval 684 pairs a pairs_valid htmp).seq
    (SourceControls.cutoff_eval (copyManyState pairs a) htmp')
  simpa only [hR,stageCost,Nat.add_assoc,stage,staged] using h

theorem export_eval (a : Data) (htmp : a.stacks 684 = []) :
    Eval exportResult (exportCost a) a (exported a) :=
  (SubexpSetupStorage.copy_eval 561 62 684 a (by decide) (by decide) (by decide) htmp).seq
    (clearMany_eval workerPorts (copyState 561 62 a))

/-- The middle execution is the exact closed service above; its denotation
and bound come from nativeFactor_run and the concrete Source command. -/
theorem command_eval (a b : Data) (n : ℕ) (ha : a.stacks 684 = [])
    (hb : b.stacks 684 = []) (he : Eval service n (staged a) b) :
    Eval command (stageCost a+(n+exportCost b)) a (exported b) :=
  (stage_eval a ha).seq (he.seq (export_eval b hb))

theorem mem_workerPorts (i : Fin 768) : i ∈ workerPorts ↔ 340 ≤ i.val ∧ i.val < 680 := by
  simp only [workerPorts,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change 340+j.val=i.val at hv
    omega
  · intro hi
    refine ⟨⟨i.val-340,by omega⟩,?_⟩
    apply Fin.ext
    change 340+(i.val-340)=i.val
    omega

theorem exported_output (a : Data) (h62 : a.stacks 62 = []) :
    (exported a).stacks 62 = a.stacks 561 := by
  rw [exported,clearMany_stacks,ite_eq_right (by decide)]
  simp [copyState,StackRoutines.copyStacks,h62]

theorem exported_clean (a : Data) (i : Fin 768) (hi : 340 ≤ i.val ∧ i.val < 680) :
    (exported a).stacks i = [] := by
  rw [exported,clearMany_stacks,ite_eq_left ((mem_workerPorts i).mpr hi)]

end SubexponentialSAT.SqrtLog.LeafProgram.Incidence

end OAI.Algorithms

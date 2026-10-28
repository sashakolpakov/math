import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorageCost

namespace OAI.Algorithms

/-! Protect the target-jet caches while the source-polynomial initializer
uses the same private local ports. Source length and target jet order are
independent runtime values. These are actual copy and clear programs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging

open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

abbrev Data := State 16 768
def savePairs : List (Fin 768 × Fin 768) :=
  [(532,680),(533,681),(582,682),(583,683)]
def restorePairs : List (Fin 768 × Fin 768) :=
  [(680,532),(681,533),(682,582),(683,583)]
def cachePorts : List (Fin 768) := [532,533,582,583]
def backupPorts : List (Fin 768) := [680,681,682,683]

abbrev before : Cmd 16 768 := .seq (copyMany 684 savePairs) (clearMany cachePorts)
def saved (a : Data) : Data := clearManyState cachePorts (copyManyState savePairs a)
def beforeCost (a : Data) : ℕ :=
  copyManyCost savePairs a + clearManyCost cachePorts (copyManyState savePairs a)

private theorem save_valid : ∀p∈savePairs,p.1≠p.2 ∧ p.1≠684 ∧ (684 : Fin 768)≠p.2 := by
  intro p hp
  simp only [savePairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl <;> decide
private theorem restore_valid : ∀p∈restorePairs,p.1≠p.2 ∧ p.1≠684 ∧ (684 : Fin 768)≠p.2 := by
  intro p hp
  simp only [restorePairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl <;> decide

theorem before_eval (a : Data) (htmp : a.stacks 684=[]) :
    Eval before (beforeCost a) a (saved a) :=
  (copyMany_eval 684 savePairs a save_valid htmp).seq
    (clearMany_eval cachePorts (copyManyState savePairs a))

theorem saved_empty (a : Data) (i : Fin 768) (hi : i∈cachePorts) :
    (saved a).stacks i=[] := by
  simp [saved,clearMany_stacks,hi]

theorem saved_values (a : Data) (h : ∀i∈backupPorts,a.stacks i=[]) :
    (saved a).stacks 680=a.stacks 532 ∧
    (saved a).stacks 681=a.stacks 533 ∧
    (saved a).stacks 682=a.stacks 582 ∧
    (saved a).stacks 683=a.stacks 583 := by
  have h0:=h 680 (by simp [backupPorts])
  have h1:=h 681 (by simp [backupPorts])
  have h2:=h 682 (by simp [backupPorts])
  have h3:=h 683 (by simp [backupPorts])
  simp [saved,clearMany_stacks,cachePorts,savePairs,copyManyState,copyState,
    StackRoutines.copyStacks,h0,h1,h2,h3]

/-- Source controls are no longer needed by inner jet preparation. Preserve
the explicitly prepared arithmetic masters and the restored target caches. -/
def retainedLow : List (Fin 205) := [5,10,104,192,193,194,201,202,203,204]
def lowPort (i : Fin 205) : Fin 768 := ⟨340+i.val,by omega⟩
def lowClearPorts : List (Fin 768) :=
  ((List.finRange 205).filter (fun i => i∉retainedLow)).map lowPort

def restored (a : Data) : Data :=
  clearManyState backupPorts (copyManyState restorePairs (clearManyState cachePorts a))
abbrev after : Cmd 16 768 := .seq (clearMany cachePorts)
  (.seq (copyMany 684 restorePairs) (.seq (clearMany backupPorts) (clearMany lowClearPorts)))
def finished (a : Data) : Data := clearManyState lowClearPorts (restored a)
def afterCost (a : Data) : ℕ :=
  clearManyCost cachePorts a + copyManyCost restorePairs (clearManyState cachePorts a) +
  clearManyCost backupPorts (copyManyState restorePairs (clearManyState cachePorts a)) +
  clearManyCost lowClearPorts (restored a)

theorem after_eval (a : Data) (htmp : a.stacks 684=[]) :
    Eval after (afterCost a) a (finished a) := by
  have htmp' : (clearManyState cachePorts a).stacks 684=[] := by
    simpa [clearMany_stacks,cachePorts] using htmp
  have h := (clearMany_eval cachePorts a).seq
    ((copyMany_eval 684 restorePairs (clearManyState cachePorts a) restore_valid htmp').seq
      ((clearMany_eval backupPorts (copyManyState restorePairs (clearManyState cachePorts a))).seq
        (clearMany_eval lowClearPorts (restored a))))
  change Eval after
    (clearManyCost cachePorts a + (copyManyCost restorePairs (clearManyState cachePorts a) +
      (clearManyCost backupPorts (copyManyState restorePairs (clearManyState cachePorts a)) +
        clearManyCost lowClearPorts (restored a)))) a (finished a) at h
  rw [show afterCost a = clearManyCost cachePorts a +
    (copyManyCost restorePairs (clearManyState cachePorts a) +
      (clearManyCost backupPorts (copyManyState restorePairs (clearManyState cachePorts a)) +
        clearManyCost lowClearPorts (restored a))) by unfold afterCost; omega]
  exact h

theorem lowClear_iff (i : Fin 768) :
    i∈lowClearPorts ↔ ∃j : Fin 205, j∉retainedLow ∧ lowPort j=i := by
  simp [lowClearPorts,List.mem_map,List.mem_filter]

theorem retained_not_cleared (j : Fin 205) (hj : j∈retainedLow) :
    lowPort j∉lowClearPorts := by
  rw [lowClear_iff]
  rintro ⟨k,hk,hkj⟩
  have hv:=congrArg Fin.val hkj
  have he : k=j := by apply Fin.ext; simpa [lowPort] using hv
  exact hk (he ▸ hj)

theorem outside_not_cleared (i : Fin 768) (hi : 545 ≤ i.val) : i∉lowClearPorts := by
  rw [lowClear_iff]
  rintro ⟨j,_,he⟩
  have hv:=congrArg Fin.val he
  simp only [lowPort] at hv
  omega

theorem finished_values (a : Data) :
    (finished a).stacks 532=a.stacks 680 ∧
    (finished a).stacks 533=a.stacks 681 ∧
    (finished a).stacks 582=a.stacks 682 ∧
    (finished a).stacks 583=a.stacks 683 := by
  have h532 : (532 : Fin 768)∉lowClearPorts := retained_not_cleared 192 (by simp [retainedLow])
  have h533 : (533 : Fin 768)∉lowClearPorts := retained_not_cleared 193 (by simp [retainedLow])
  have h582 := outside_not_cleared 582 (by decide)
  have h583 := outside_not_cleared 583 (by decide)
  simp [finished,restored,clearMany_stacks,cachePorts,backupPorts,restorePairs,
    copyManyState,copyState,StackRoutines.copyStacks,h532,h533,h582,h583]

theorem finished_backups (a : Data) (i : Fin 768) (hi : i∈backupPorts) :
    (finished a).stacks i=[] := by
  simp [finished,clearMany_stacks,restored,hi]

theorem finished_low (a : Data) (j : Fin 205) (hj : j∉retainedLow) :
    (finished a).stacks (lowPort j)=[] := by
  simp [finished,clearMany_stacks,(lowClear_iff _).mpr ⟨j,hj,rfl⟩]

end SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging

end OAI.Algorithms

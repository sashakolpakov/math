import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSource

namespace OAI.Algorithms

/-! Exact store restoration for the executed source callback. The source
kernel may change its four initialized caches and source output; the wrapper
restores all four caches and removes every staged source control. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

private theorem control_classified (p : Fin 768 × Fin 768) (hp : p ∈ SourceControls.pairs) :
    p.2 ∈ SourceStaging.lowClearPorts ∨ p.2 ∈ SourceControls.extraPorts := by
  simp only [SourceControls.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide

private theorem controls_frame (a : Data) (i : Fin 768)
    (hlow : i ∉ SourceStaging.lowClearPorts) (hextra : i ∉ SourceControls.extraPorts) :
    (SourceControls.prepared a).stacks i = a.stacks i := by
  have hi365 : i ≠ 365 := by intro h; subst i; exact hlow (by decide)
  unfold SourceControls.prepared
  rw [SourceControls.delta_stacks,Function.update_of_ne hi365]
  apply copyMany_frame
  intro p hp he
  rcases control_classified p hp with h|h
  · exact hlow (he.symm ▸ h)
  · exact hextra (he.symm ▸ h)

private theorem saved_frame (a : Data) (i : Fin 768)
    (hc : i ∉ SourceStaging.cachePorts) (hb : i ∉ SourceStaging.backupPorts) :
    (SourceStaging.saved a).stacks i = a.stacks i := by
  rw [SourceStaging.saved,clearMany_stacks,ite_eq_right hc]
  apply copyMany_frame
  intro p hp he
  have hdest : p.2 ∈ SourceStaging.backupPorts := by
    simp only [SourceStaging.savePairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with h|h|h|h <;> subst p <;> decide
  exact hb (he.symm ▸ hdest)

private theorem prepared_frame (a : Data) (i : Fin 768)
    (hlow : i ∉ SourceStaging.lowClearPorts) (hextra : i ∉ SourceControls.extraPorts)
    (hc : i ∉ SourceStaging.cachePorts) (hb : i ∉ SourceStaging.backupPorts) :
    (prepared a).stacks i = a.stacks i :=
  (controls_frame _ i hlow hextra).trans (saved_frame a i hc hb)

private theorem restored_frame (a : Data) (i : Fin 768)
    (hc : i ∉ SourceStaging.cachePorts) (hb : i ∉ SourceStaging.backupPorts) :
    (SourceStaging.restored a).stacks i = a.stacks i := by
  rw [SourceStaging.restored,clearMany_stacks,ite_eq_right hb]
  rw [copyMany_frame _ _ _ (by
    intro p hp he
    have hdest : p.2 ∈ SourceStaging.cachePorts := by
      simp only [SourceStaging.restorePairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with h|h|h|h <;> subst p <;> decide
    exact hc (he.symm ▸ hdest))]
  rw [clearMany_stacks,ite_eq_right hc]

def coreChanged : List (Fin 768) := [545,532,533,582,583]
def CoreFrame (a : Data) (b : State 16 340) : Prop :=
  ∀ i, i ∉ coreChanged → (coreOutput a b).stacks i = (prepared a).stacks i

/-- Native source-row correctness gives the local frame below; relocation
transports it without imposing any condition on unrelated global masters. -/
theorem coreFrame_of_local (a : Data) (b : State 16 340)
    (h : ∀ j : Fin 340, j ∉ ([205,192,193,242,243] : List (Fin 340)) →
      b.stacks j = (prepared a).stacks (workerPort j)) : CoreFrame a b := by
  intro i hi
  by_cases hin : ∃ j, workerPort j = i
  · obtain ⟨j,rfl⟩ := hin
    rw [show (coreOutput a b).stacks (workerPort j) = b.stacks j from
      embedState_stack id workerPort (prepared a) b workerPort_injective j]
    apply h
    intro hj
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hj
    rcases hj with hj|hj|hj|hj|hj <;> subst j <;> exact hi (by decide)
  · exact embedState_stack_frame id workerPort (prepared a) b i hin

private theorem prepared_backups (a : Data)
    (hb : ∀ i ∈ SourceStaging.backupPorts, a.stacks i = []) :
    (prepared a).stacks 680 = a.stacks 532 ∧
    (prepared a).stacks 681 = a.stacks 533 ∧
    (prepared a).stacks 682 = a.stacks 582 ∧
    (prepared a).stacks 683 = a.stacks 583 := by
  have h := SourceStaging.saved_values a hb
  simpa only [prepared,controls_frame _ 680 (by decide) (by decide),
    controls_frame _ 681 (by decide) (by decide),
    controls_frame _ 682 (by decide) (by decide),
    controls_frame _ 683 (by decide) (by decide)] using h

private theorem finished_caches (a : Data) (b : State 16 340)
    (hf : CoreFrame a b) (hb : ∀ i ∈ SourceStaging.backupPorts, a.stacks i = []) :
    (finished a b).stacks 532 = a.stacks 532 ∧
    (finished a b).stacks 533 = a.stacks 533 ∧
    (finished a b).stacks 582 = a.stacks 582 ∧
    (finished a b).stacks 583 = a.stacks 583 := by
  have hv := SourceStaging.finished_values (coreOutput a b)
  have hp := prepared_backups a hb
  have h680 := hf 680 (by decide)
  have h681 := hf 681 (by decide)
  have h682 := hf 682 (by decide)
  have h683 := hf 683 (by decide)
  rw [h680,h681,h682,h683] at hv
  rw [hp.1,hp.2.1,hp.2.2.1,hp.2.2.2] at hv
  simpa only [finished,SourceControls.cleaned_frame _ 532 (by decide),
    SourceControls.cleaned_frame _ 533 (by decide),
    SourceControls.cleaned_frame _ 582 (by decide),
    SourceControls.cleaned_frame _ 583 (by decide)] using hv

theorem finished_stacks (a : Data) (b : State 16 340)
    (hf : CoreFrame a b)
    (hlow : ∀ i ∈ SourceStaging.lowClearPorts, a.stacks i = [])
    (hextra : ∀ i ∈ SourceControls.extraPorts, a.stacks i = [])
    (hb : ∀ i ∈ SourceStaging.backupPorts, a.stacks i = []) :
    (finished a b).stacks = Function.update a.stacks 545 (b.stacks 205) := by
  funext i
  by_cases hi : i = 545
  · subst i; simpa using finished_rows a b
  rw [Function.update_of_ne hi]
  by_cases he : i ∈ SourceControls.extraPorts
  · rw [finished,SourceControls.cleaned,clearMany_stacks,ite_eq_left he,hextra i he]
  by_cases hl : i ∈ SourceStaging.lowClearPorts
  · rw [finished,SourceControls.cleaned,clearMany_stacks,ite_eq_right he,
      SourceStaging.finished,clearMany_stacks,ite_eq_left hl,hlow i hl]
  by_cases hbackup : i ∈ SourceStaging.backupPorts
  · rw [finished,SourceControls.cleaned,clearMany_stacks,ite_eq_right he,
      SourceStaging.finished_backups _ i hbackup,hb i hbackup]
  by_cases hc : i ∈ SourceStaging.cachePorts
  · have hv := finished_caches a b hf hb
    simp only [SourceStaging.cachePorts,List.mem_cons,List.mem_nil_iff,or_false] at hc
    rcases hc with h|h|h|h <;> subst i
    · exact hv.1
    · exact hv.2.1
    · exact hv.2.2.1
    · exact hv.2.2.2
  · rw [finished,SourceControls.cleaned,clearMany_stacks,ite_eq_right he,
      SourceStaging.finished,clearMany_stacks,ite_eq_right hl,restored_frame _ i hc hbackup]
    rw [hf i (by simpa [coreChanged,SourceStaging.cachePorts,hi] using hc)]
    exact prepared_frame a i hl he hc hbackup

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms

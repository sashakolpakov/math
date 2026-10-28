import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceControls
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramConcrete

namespace OAI.Algorithms

/-! The source callback used by the actual incidence-table loop. The fixed
command stages source controls, protects all four target caches, invokes the
concrete source-row instruction table, restores the target caches, and clears
source-only controls. The local source correctness theorem is joined below
through its actual execution, never through a supplied polynomial oracle. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
abbrev Data := State 16 768

def workerPort (i : Fin 340) : Fin 768 := ⟨340+i.val,by omega⟩
theorem workerPort_injective : Function.Injective workerPort := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 340+i.val=340+j.val at hv
  omega

abbrev core : Cmd 16 768 := .call (ProgramLinking.liftProgram
  LayoutSourceRowsProgram.sourceRowsProgram id workerPort)
abbrev command : Cmd 16 768 := .seq SourceStaging.before
  (.seq SourceControls.prepare (.seq core
    (.seq SourceStaging.after SourceControls.cleanup)))

def prepared (a : Data) : Data := SourceControls.prepared (SourceStaging.saved a)
noncomputable def coreOutput (a : Data) (b : State 16 340) : Data :=
  embedState id workerPort (prepared a) b
noncomputable def finished (a : Data) (b : State 16 340) : Data :=
  SourceControls.cleaned (SourceStaging.finished (coreOutput a b))
noncomputable def cost (a : Data) (b : State 16 340) (n : ℕ) : ℕ :=
  SourceStaging.beforeCost a + (SourceControls.prepareCost (SourceStaging.saved a) +
    (n+1 + (SourceStaging.afterCost (coreOutput a b) +
      clearManyCost SourceControls.extraPorts (SourceStaging.finished (coreOutput a b)))))

private theorem saved_tmp (a : Data) :
    (SourceStaging.saved a).stacks 684 = a.stacks 684 := by
  rw [SourceStaging.saved,clearMany_stacks,ite_eq_right (by decide)]
  apply copyMany_frame
  intro p hp
  simp only [SourceStaging.savePairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with h|h|h|h <;> subst p <;> decide

private theorem prepared_tmp (a : Data) : (prepared a).stacks 684 = a.stacks 684 := by
  unfold prepared SourceControls.prepared
  rw [SourceControls.delta_stacks]
  simp only [Function.update_of_ne (by decide : (684 : Fin 768) ≠ 365)]
  calc
    (copyManyState SourceControls.pairs (SourceStaging.saved a)).stacks 684 =
        (SourceStaging.saved a).stacks 684 := by
      apply copyMany_frame
      intro p hp
      exact (SourceControls.pairs_valid p hp).2.2
    _ = a.stacks 684 := saved_tmp a

private theorem coreOutput_tmp (a : Data) (b : State 16 340) :
    (coreOutput a b).stacks 684 = a.stacks 684 := by
  have h := embedState_stack_frame id workerPort (prepared a) b (684 : Fin 768) (by
    rintro ⟨i,hi⟩
    have hv := congrArg Fin.val hi
    change 340+i.val=684 at hv
    omega)
  exact h.trans (prepared_tmp a)

/-- This composition lemma charges the concrete source command's execution
plus every staging/cleanup call. The source execution premise is precisely
what its native correctness theorem supplies. -/
theorem command_eval (a : Data) (b : State 16 340) (n : ℕ)
    (htmp : a.stacks 684 = [])
    (hsource : Eval LayoutSourceRowsProgram.sourceRows n
      (projectState id workerPort (prepared a)) b) :
    Eval command (cost a b n) a (finished a b) := by
  have h0 := SourceStaging.before_eval a htmp
  have h1 := SourceControls.prepare_eval (SourceStaging.saved a)
    ((saved_tmp a).trans htmp)
  have h2 := eval_call_from_state LayoutSourceRowsProgram.sourceRowsProgram
    id workerPort (prepared a) Function.injective_id workerPort_injective
    (compiled_halt_trace hsource 337 205)
  have h3 := SourceStaging.after_eval (coreOutput a b)
    ((coreOutput_tmp a b).trans htmp)
  have h4 := SourceControls.cleanup_eval (SourceStaging.finished (coreOutput a b))
  exact h0.seq (h1.seq (h2.seq (h3.seq h4)))

theorem finished_rows (a : Data) (b : State 16 340) :
    (finished a b).stacks 545 = b.stacks 205 := by
  unfold finished
  rw [SourceControls.cleaned_frame _ _ (by decide)]
  rw [SourceStaging.finished,clearMany_stacks,
    ite_eq_right (SourceStaging.outside_not_cleared 545 (by decide))]
  unfold SourceStaging.restored
  rw [clearMany_stacks,ite_eq_right (by decide)]
  rw [copyMany_frame _ _ _ (by
    intro p hp
    simp only [SourceStaging.restorePairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with h|h|h|h <;> subst p <;> decide)]
  rw [clearMany_stacks,ite_eq_right (by decide)]
  exact embedState_stack id workerPort (prepared a) b workerPort_injective 205

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms

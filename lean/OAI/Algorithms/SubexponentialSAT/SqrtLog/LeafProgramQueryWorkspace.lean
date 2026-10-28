import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryBranches

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The branch invariant need only retain persistent outer workspace cells;
all generated query-local data are reclaimed after the branch sum. -/
def ProtectedWork (base : Data) (work : Fin 763 → List Bool) : Prop :=
  ∀i,Protected (Marked.Wide.workPort i) → work i=base.stacks (Marked.Wide.workPort i)

 theorem protected_frame_of_workspace (base b : Data)
    (hw : ProtectedWork base (Marked.Wide.workspace b))
    (h320 : b.stacks 320=base.stacks 320) (h322 : b.stacks 322=base.stacks 322)
    (i : Fin 768) (hi : Protected i) (h323 : i≠323) : b.stacks i=base.stacks i := by
  by_cases h : i=320
  · subst i; exact h320
  by_cases h' : i=322
  · subst i; exact h322
  have hlo : 700 ≤ i.val := by
    simp only [Protected] at hi
    rcases hi with hi|hi|hi|hi|hi|hi|hi|hi|hi
    · exact False.elim (h hi)
    · exact False.elim (h' hi)
    · exact False.elim (h323 hi)
    all_goals first | (subst i; decide) | omega
  let j : Fin 763 := ⟨i.val-5,by omega⟩
  have hj : Marked.Wide.workPort j=i := by
    apply Fin.ext
    simp only [Marked.Wide.workPort]
    dsimp [j]
    split_ifs <;> simp only <;> omega
  have hh := hw j (hj.symm ▸ hi)
  simpa only [Marked.Wide.workspace,hj] using hh

/-- Concrete branch execution followed by cleanup restores the original
collector workspace, while retaining the newly computed count on323. -/
theorem branches_restore (residual : Code) (base a : Data) (hc : CleanWork base)
    (h320 : a.stacks 320=base.stacks 320) (h322 : a.stacks 322=base.stacks 322)
    (count B width W : ℕ)
    (ctx : Marked.Wide.BranchContext residual (Marked.Wide.maskCopied a)
      (ProtectedWork base) count B width)
    (htmp : a.stacks 339=[]) (hw : ∀i,(a.stacks i).length ≤ W) :
    ∃ n b, n ≤ branchBudget a B W ∧ Eval (branches residual) n a b ∧
      Marked.Wide.workspace b=Marked.Wide.workspace base ∧
      b.stacks 320=base.stacks 320 ∧ b.stacks 322=base.stacks 322 ∧
      BinaryArithmetic.toNat (b.stacks 323)=count ∧ (b.stacks 323).length ≤ width ∧
      b.regs 16=false ∧ b.regs 17=true ∧ b.regs 18=false ∧
      b.stacks 321=[] ∧ b.stacks 324=[] := by
  obtain ⟨n,middle,hn,he,hs,ha,hv,hl,hclean,h16,h17,h18,hready⟩ :=
    branches_eval residual a (ProtectedWork base) count B width W ctx htmp hw
  have ms : middle.stacks 320=base.stacks 320 := by
    rw [cleaned_frame middle 320 (by decide)] at hs
    exact hs.trans h320
  have ma : middle.stacks 322=base.stacks 322 := by
    rw [cleaned_frame middle 322 (by decide)] at ha
    exact ha.trans h322
  refine ⟨n,cleaned middle,hn,he,?_,hs.trans h320,ha.trans h322,hv,hl,h16,h17,h18,
    hclean 321 (by decide),hclean 324 (by decide)⟩
  exact cleanup_restores_workspace base middle hc
    (protected_frame_of_workspace base middle hready ms ma)

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms

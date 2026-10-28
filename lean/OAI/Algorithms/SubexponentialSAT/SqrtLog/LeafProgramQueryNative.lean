import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQuerySetup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryWorkspace

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

 theorem prepared_reader_frame (a : Data) (i : Fin 768)
    (hlo : 320 ≤ i.val) (hhi : i.val < 323) : (prepared a).stacks i=a.stacks i := by
  have hport : i∉Count.Prepare.ports := by
    intro hm
    simp only [Count.Prepare.ports,List.mem_dedup,List.mem_append] at hm
    rcases hm with hm|hm
    · obtain ⟨j,hj,hji⟩ := List.mem_map.mp hm
      have hval := congrArg Fin.val hji
      change j.val=i.val at hval
      have hjlt := j.isLt
      omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with h|h|h|h|h|h|h <;>
        have hh := congrArg Fin.val h <;> norm_num at hh <;> omega
  have hn (j : Fin 768) (hj : j.val < 320) : i≠j := by
    intro h
    have hh := congrArg Fin.val h
    omega
  exact (Count.Prepare.output_frame (Samples.prepared a) i hport
    (by intro h; have hh : i.val=699 := congrArg Fin.val h; omega)).trans
      (Samples.prepared_frame a i (hn _ (by decide)) (hn _ (by decide)))

 theorem Preparation.temporary_frame {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Preparation q k a hg W V L) :
    (prepared p.out).stacks 339=a.stacks 339 := by
  have hf := p.frontOutput.frame 339 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by intro j; fin_cases j <;> decide)
  have hp := p.packingFrame 339 (by decide) (by decide) (by decide)
  have ha := p.arithmeticOutput.collectorFrame 339 (by decide) (by decide)
  exact (Count.Prepare.output_high_frame (Samples.prepared p.out) 339 (by decide) (by decide)).trans
    ((Samples.prepared_frame p.out 339 (by decide) (by decide)).trans
      (ha.trans (hp.trans hf)))

/-- All setup executions here are supplied by `Preparation`, which is constructed
from input masters by `prepare_native`. The sole remaining semantic interface
is the concrete residual branch specification. -/
theorem command_from_preparation (q : LeafQueryFrontend.Query) (k : ℕ) (base a : Data)
    (hg : Guard (q.input k)) (W V L : ℕ) (p : Preparation q k a hg W V L)
    (hc : CleanWork base) (h320 : a.stacks 320=base.stacks 320)
    (h322 : a.stacks 322=base.stacks 322) (h339 : a.stacks 339=[])
    (hw : ∀i,(a.stacks i).length ≤ W) (count B width : ℕ)
    (ctx : Marked.Wide.BranchContext Residual.command (Marked.Wide.maskCopied (prepared p.out))
      (ProtectedWork base) count B width) :
    let U := W+p.frontSteps+p.packingSteps+p.arithmeticSteps+prepareCost p.out
    ∃ n b, n ≤ p.frontSteps+p.packingSteps+p.arithmeticSteps+prepareCost p.out+
        branchBudget (prepared p.out) B U+1 ∧
      Eval (command k) n a b ∧ Marked.Wide.workspace b=Marked.Wide.workspace base ∧
      b.stacks 320=base.stacks 320 ∧ b.stacks 322=base.stacks 322 ∧
      BinaryArithmetic.toNat (b.stacks 323)=count ∧ (b.stacks 323).length ≤ width ∧
      b.regs 16=false ∧ b.regs 17=true ∧ b.regs 18=false ∧
      b.stacks 321=[] ∧ b.stacks 324=[] := by
  dsimp only
  have hs320 : (prepared p.out).stacks 320=base.stacks 320 :=
    (prepared_reader_frame p.out 320 (by decide) (by decide)).trans
      ((p.protected_frame 320 (by decide)).trans h320)
  have hs322 : (prepared p.out).stacks 322=base.stacks 322 :=
    (prepared_reader_frame p.out 322 (by decide) (by decide)).trans
      ((p.protected_frame 322 (by decide)).trans h322)
  have ht := p.temporary_frame.trans h339
  have hwp := eval_width (prepare_eval p.out)
    (W+p.frontSteps+p.packingSteps+p.arithmeticSteps) (p.output_width hw)
  obtain ⟨nb,b,hnb,he,hwork,hs,hm,hv,hl,h16,h17,h18,h321,h324⟩ :=
    branches_restore Residual.command base (prepared p.out) hc hs320 hs322 count B width
      _ ctx ht hwp
  refine ⟨p.frontSteps+(p.packingSteps+(p.arithmeticSteps+(prepareCost p.out+nb))+1),b,
    by omega,?_,hwork,hs,hm,hv,hl,h16,h17,h18,h321,h324⟩
  exact p.frontExecution.seq (.ite_true (p.frontOutput.guard.mpr hg)
    (p.packingExecution.seq (p.arithmeticExecution.seq ((prepare_eval p.out).seq he))))

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms

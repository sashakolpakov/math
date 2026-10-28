import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeStage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeExport
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryMaskedNative

namespace OAI.Algorithms

/-! The actual final-count adapter: stage the exact raw rows and padded width,
run the native accepted query, export its binary result, and reclaim workspace.
The prepared endpoint below is conditional on the explicit native branch
context; it does not claim that context as an oracle. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT BitProgram StructuredCalls LeafOuterProgram

noncomputable def acceptedCount (k : ℕ) : Cmd 40 896 :=
  .seq stageFinal (.seq (workerCall (LeafProgram.Query.accepted k))
    (.seq (exportWorker 323 788) (.call (StackRoutines.clearProgram 787 0 1))))

noncomputable def acceptedOutput (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,Function.update a.stacks 787 []⟩

noncomputable def acceptedCost (a : Data) (n : ℕ) (b : State 40 768) : ℕ :=
  stageFinalCost a+(n+1)+(exportCost 323 788 (workerResult (finalStaged a) b))+
    2*(a.stacks 787).length+3

theorem accepted_eval_of_native (k : ℕ) (a : Data) (ht : a.stacks 767=[])
    (n : ℕ) (b : State 40 768)
    (he : Eval (LeafProgram.Query.accepted k) n (projectState id workerStack (finalStaged a)) b)
    (h767 : b.stacks 767=[]) :
    ∃ c, Eval (acceptedCount k) (acceptedCost a n b) a c ∧ c.stacks 787=[] ∧
      c.stacks 788=b.stacks 323 ∧ WorkerEmpty c ∧
      (∀ i : Fin 896, 768 ≤ i.val → i≠787 → i≠788 → c.stacks i=a.stacks i) := by
  let e := workerResult (finalStaged a) b
  let f := exportedWorker 323 788 e
  have h1 := stageFinal_eval a ht
  have h2 := workerCall_eval (LeafProgram.Query.accepted k) (finalStaged a) b n he
  have he767 : e.stacks 767=[] := (workerResult_low _ _ 767).trans h767
  have h3 := exportWorker_eval 323 (by decide) 788 (by decide) e he767
  have h4 := BankRoutines.clear_call_eval (787 : Fin 896) (0 : Fin 40) 1 f.regs f.stacks
  have hf787 : f.stacks 787=a.stacks 787 := by
    rw [exportedWorker_frame _ _ _ _ (by decide) (by decide),
      workerResult_high _ _ _ (by decide)]
    exact finalStaged_frame _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hc : (⟨readRegs f.regs 0 1 none,StackRoutines.clearStacks 787 f.stacks⟩ : Data)=
      acceptedOutput f := rfl
  rw [hc,hf787] at h4
  refine ⟨acceptedOutput f,?_,by simp [acceptedOutput],?_,?_,?_⟩
  · simpa only [acceptedCount,acceptedCost,Nat.add_assoc] using h1.seq (h2.seq (h3.seq h4))
  · simp only [acceptedOutput,Function.update_of_ne (by decide : (788 : Fin 896)≠787)]
    exact (exportedWorker_output _ _ _ (by decide)).trans (workerResult_low _ _ 323)
  · intro i
    have hn : workerStack i≠787 := by
      intro h; have := congrArg Fin.val h
      simp only [workerStack,Fin.val_castAdd] at this
      have := i.isLt; omega
    simpa only [acceptedOutput,Function.update_of_ne hn] using exportedWorker_empty 323 788 e i
  · intro i hi h787 h788
    simp only [acceptedOutput,Function.update_of_ne h787]
    rw [exportedWorker_frame _ _ _ _ hi h788,workerResult_high _ _ _ hi]
    exact finalStaged_frame _ _ (by rintro rfl; exact (by decide : ¬(768 ≤ (700 : Fin 896).val)) hi)
      (by rintro rfl; exact (by decide : ¬(768 ≤ (701 : Fin 896).val)) hi) (by rintro rfl; exact (by decide : ¬(768 ≤ (707 : Fin 896).val)) hi)
      (by rintro rfl; exact (by decide : ¬(768 ≤ (708 : Fin 896).val)) hi) (by rintro rfl; exact (by decide : ¬(768 ≤ (709 : Fin 896).val)) hi)

open LeafProgram LeafParametersProgram in
theorem accepted_from_preparation (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (ha : WorkerEmpty a) (hg : Guard (q.input k)) (W V L : ℕ)
    (p : Query.Preparation q k
      (Query.unmarkedInput (Query.Carried.reference (projectState id workerStack (finalStaged a))))
      hg W V L)
    (hw : ∀ i, ((Query.unmarkedInput (Query.Carried.reference
      (projectState id workerStack (finalStaged a)))).stacks i).length ≤ W)
    (count B width : ℕ)
    (ctx : Marked.Wide.BranchContext Residual.command (Marked.Wide.maskCopied (Query.prepared p.out))
      (Query.ProtectedWork (Query.Carried.reference (projectState id workerStack (finalStaged a))))
      count B width) :
    ∃ n b c, n ≤ 3+Query.preparationBudget p B ∧
      Eval (acceptedCount k) (acceptedCost a n b) a c ∧ c.stacks 787=[] ∧
      BinaryArithmetic.toNat (c.stacks 788)=count ∧ (c.stacks 788).length ≤ width ∧ WorkerEmpty c ∧
      (∀ i : Fin 896, 768 ≤ i.val → i≠787 → i≠788 → c.stacks i=a.stacks i) := by
  obtain ⟨n,b,hn,he,hs,_,_,hv,hl,_,_,_,_,_⟩ := Query.Carried.accepted_from_masked_preparation
    q k (projectState id workerStack (finalStaged a)) hg W V L p (final_clean a ha) hw
    count B width ctx
  have h767 : b.stacks 767=[] := by
    have hh := congrFun hs (762 : Fin 763)
    change b.stacks 767=(finalStaged a).stacks 767 at hh
    rw [hh,finalStaged_frame _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ha 767
  obtain ⟨c,hc,h787,h788,hclean,hframe⟩ := accepted_eval_of_native k a (ha 767) n b he h767
  exact ⟨n,b,c,hn,hc,h787,h788 ▸ hv,h788 ▸ hl,hclean,hframe⟩

end SubexponentialSAT.SqrtLog.LeafOuterNative

end OAI.Algorithms

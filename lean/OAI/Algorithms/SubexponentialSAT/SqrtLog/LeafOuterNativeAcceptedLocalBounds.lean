import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeAcceptedBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeWidth

namespace OAI.Algorithms

/-! The accepted-count adapter charges only its actual five source words,
two cleared output words, and the paid native query trace. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT BitProgram StructuredCalls LeafOuterProgram SubexpSetupStorage LeafProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def AcceptedSource (i : Fin 896) : Prop :=
  i=777 ∨ i=782 ∨ i=783 ∨ i=784 ∨ i=785 ∨ i=787 ∨ i=788

theorem acceptedCost_exact (a : Data) (n : ℕ) (b : State 40 768) :
    acceptedCost a n b = stageFinalCost a+(n+1)+
      (2*(a.stacks 788).length+7*(b.stacks 323).length+8+
        Cleanup.Wide.budget b+1)+2*(a.stacks 787).length+3 := by
  have hc : Cleanup.Wide.bytes (projectState id workerStack
      (routed (workerStack 323,788) (workerResult (finalStaged a) b)))=
      Cleanup.Wide.bytes b := by
    unfold Cleanup.Wide.bytes
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    have hn : workerStack i≠788 := by
      intro heq
      have hv := congrArg (fun x : Fin 896 => x.val) heq
      simp only [workerStack,Fin.val_castAdd] at hv
      have := i.isLt
      omega
    simp only [projectState,routed,Function.comp_apply,Function.update_of_ne hn,workerResult_low]
  have hd : (workerResult (finalStaged a) b).stacks 788=a.stacks 788 := by
    rw [workerResult_high _ _ _ (by decide)]
    exact finalStaged_frame a 788 (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [acceptedCost,exportCost,routeCost,workerResult_low,hd,Cleanup.Wide.budget,hc]

theorem acceptedCost_le_sources (k : ℕ) (a : Data) (L n : ℕ)
    (hw : WorkerEmpty a)
    (hs : ∀ i, AcceptedSource i → (a.stacks i).length ≤ L)
    (b : State 40 768)
    (he : Eval (Query.accepted k) n (projectState id workerStack (finalStaged a)) b) :
    acceptedCost a n b ≤ 5000*(L+n+1) := by
  have hempty (i : Fin 896) (hi : i.val < 768) : a.stacks i=[] := by
    let j : Fin 768 := ⟨i.val,hi⟩
    exact hw j
  have hstage : stageFinalCost a ≤ 5*(9*L+8)+3 := by
    have h777 := hs 777 (Or.inl rfl)
    have h782 := hs 782 (Or.inr (Or.inl rfl))
    have h783 := hs 783 (Or.inr (Or.inr (Or.inl rfl)))
    have h784 := hs 784 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    have h785 := hs 785 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    simp only [stageFinalCost,masterRoutes,routesCost,routed,routeCost]
    simp only [Function.update_of_ne (by decide : (701 : Fin 896)≠709)]
    simp [hempty 700 (by decide),hempty 701 (by decide),hempty 707 (by decide),
      hempty 708 (by decide),hempty 709 (by decide)]
    omega
  have hinit (i : Fin 768) : ((finalStaged a).stacks (workerStack i)).length ≤ L := by
    by_cases h0 : workerStack i=700
    · rw [h0,(finalStaged_sources a).1]; exact hs 784 (by simp [AcceptedSource])
    by_cases h1 : workerStack i=701
    · rw [h1,(finalStaged_sources a).2.1]; exact hs 777 (Or.inl rfl)
    by_cases h7 : workerStack i=707
    · rw [h7,(finalStaged_sources a).2.2.1]; exact hs 782 (by simp [AcceptedSource])
    by_cases h8 : workerStack i=708
    · rw [h8,(finalStaged_sources a).2.2.2.1]; exact hs 783 (by simp [AcceptedSource])
    by_cases h9 : workerStack i=709
    · rw [h9,(finalStaged_sources a).2.2.2.2]; exact hs 785 (by simp [AcceptedSource])
    rw [finalStaged_frame a (workerStack i) h0 h1 h7 h8 h9,hw i]
    simp
  have hout (i : Fin 768) : (b.stacks i).length ≤ L+n+1 := by
    have h := eval_stack_length he i
    have hi := hinit i
    change (b.stacks i).length ≤ ((finalStaged a).stacks (workerStack i)).length+n+1 at h
    omega
  have hsum : ((List.finRange 768).map (fun i => (b.stacks i).length)).sum ≤
      (List.finRange 768).length*(L+n+1) := by
    induction List.finRange 768 with
    | nil => simp
    | cons i is ih =>
        simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
        have hi := hout i
        omega
  simp only [List.length_finRange] at hsum
  have h323 := hout 323
  have h787 := hs 787 (by simp [AcceptedSource])
  have h788 := hs 788 (by simp [AcceptedSource])
  rw [acceptedCost_exact]
  unfold Cleanup.Wide.budget Cleanup.Wide.bytes
  omega

theorem accepted_bounded_of_native_sources (k : ℕ) (a : Data) (L Q n : ℕ)
    (hw : WorkerEmpty a)
    (hs : ∀ i, AcceptedSource i → (a.stacks i).length ≤ L)
    (b : State 40 768)
    (he : Eval (Query.accepted k) n (projectState id workerStack (finalStaged a)) b)
    (hn : n ≤ Q) (h767 : b.stacks 767=[]) :
    ∃ t c, t ≤ 5000*(L+Q+1) ∧ Eval (acceptedCount k) t a c ∧ c.stacks 787=[] ∧
      c.stacks 788=b.stacks 323 ∧ WorkerEmpty c ∧
      (∀ i : Fin 896, 768 ≤ i.val → i≠787 → i≠788 → c.stacks i=a.stacks i) := by
  obtain ⟨c,hc,h787,h788,hclean,hf⟩ := accepted_eval_of_native k a (hw 767) n b he h767
  have hb := acceptedCost_le_sources k a L n hw hs b he
  exact ⟨acceptedCost a n b,c,hb.trans (by omega),hc,h787,h788,hclean,hf⟩

end SubexponentialSAT.SqrtLog.LeafOuterNative

end OAI.Algorithms

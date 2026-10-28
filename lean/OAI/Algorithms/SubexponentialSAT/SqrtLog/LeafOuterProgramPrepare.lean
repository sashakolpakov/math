import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramPrepareCode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramParameters

namespace OAI.Algorithms

/-! Exact arithmetic preparation, cleanup, and preservation of the decoder's
physical width. The only incoming numerical data are n, m and B. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

private theorem hash_stack_val (j : Fin 14) :
    (LeafProgram.HashParameters.ports.hash.stack j).val = 768+j.val := by
  fin_cases j <;> rfl

private theorem parameter_stack_small (j : Fin 44)
    (h14 : j ≠ 14) (h15 : j ≠ 15) (h16 : j ≠ 16) :
    (LeafProgram.HashParameters.ports.stack j).val < 782 := by
  fin_cases j <;> simp_all [LeafProgram.HashParameters.ports,LeafProgram.HashParameters.stackMap]

def prepareHashBudget (L : ℕ) : ℕ :=
  let c := 10000000000*(L+1)^2+1
  c+1536*(L+c)+2348

theorem prepareHash_eval (a : Data) (L : ℕ) (hW : WordBound L a)
    (hr : Execution.HashInputs.Ready (projectState
      LeafProgram.HashParameters.ports.hash.register LeafProgram.HashParameters.ports.hash.stack a))
    (hm : BinaryArithmetic.toNat (a.stacks 782) ≠ 0) (ht : a.stacks 767=[]) :
    ∃ t ≤ prepareHashBudget L, ∃ b,
      Eval prepareHash t a b ∧ WorkerEmpty b ∧
      Execution.HashInputs.Ready (projectState
        LeafProgram.HashParameters.ports.hash.register LeafProgram.HashParameters.ports.hash.stack b) ∧
      BinaryArithmetic.toNat (b.stacks 768)=3*BinaryArithmetic.toNat (a.stacks 782) ∧
      BinaryArithmetic.toNat (b.stacks 773)=SparseCode.distanceDenom
        (BinaryArithmetic.toNat (a.stacks 782)) (BinaryArithmetic.toNat (a.stacks 786)) ∧
      BinaryArithmetic.toNat (b.stacks 774)=HashSelect.loopCap
        (BinaryArithmetic.toNat (a.stacks 785)) (BinaryArithmetic.toNat (a.stacks 782)) ∧
      b.stacks 777=a.stacks 777 ∧
      (∀ i : Fin 896, 782 ≤ i.val → b.stacks i=a.stacks i) := by
  let p := LeafProgram.HashParameters.ports
  obtain ⟨t,htb,c,he,hready,h0,h5,h6,h9,hf,hout,_⟩ :=
    Execution.HashParameters.command_eval p a L (fun i => hW (p.stack i)) hr hm
  have hc767 : c.stacks 767=[] := (hout 767 (by decide)).trans ht
  have hcW : WordBound (L+(10000000000*(L+1)^2+1)) c :=
    SubexpSetupBoundSpec.wordBound_mono (SubexpSetupBoundSpec.eval_wordBound hW he) (by omega)
  have hclean := clearWorker_eval c hc767
  have hcost := cleanup_budget_le c _ hcW
  have cf (i : Fin 896) (hi : 782 ≤ i.val) : c.stacks i=a.stacks i := by
    by_cases hj : ∃ j, p.stack j=i
    · obtain ⟨j,rfl⟩ := hj
      have cases : j=14 ∨ j=15 ∨ j=16 := by
        by_contra hn
        push Not at hn
        have hh := parameter_stack_small j hn.1 hn.2.1 hn.2.2
        change (p.stack j).val < 782 at hh
        omega
      rcases cases with rfl|rfl|rfl
      all_goals apply hf <;> first | (rw [HashParametersProgram.ABI.work_mem]; decide) | decide
    · exact hout i (by intro j h; exact hj ⟨j,h⟩)
  refine ⟨_,?_,workerCleared c,he.seq hclean,?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp only [prepareHashBudget]; omega
  · exact clearWorker_stack c
  · intro j hj0 hj5 hj6 hj9
    change (workerCleared c).stacks (p.hash.stack j)=[]
    rw [clearWorker_frame c _ (by have hv : (p.hash.stack j).val=768+j.val := hash_stack_val j; omega)]
    exact hready j hj0 hj5 hj6 hj9
  · rw [clearWorker_frame c 768 (by decide)]; exact h0
  · rw [clearWorker_frame c 773 (by decide)]; exact h5
  · rw [clearWorker_frame c 774 (by decide)]; exact h6
  · rw [clearWorker_frame c 777 (by decide)]; exact h9
  · intro i hi
    exact (clearWorker_frame c i (by omega)).trans (cf i hi)

theorem saveWidth_eval (a : Data) (ht : a.stacks 767=[]) :
    Eval saveWidth (2*(a.stacks 783).length+7*(a.stacks 768).length+8)
      a (routed (768,783) a) := route_eval (768,783) (by unfold routeValid; decide) a ht

theorem saveWidth_value (a : Data) :
    (routed (768,783) a).stacks 783=a.stacks 768 := by simp [routed]

theorem saveWidth_frame (a : Data) (i : Fin 896) (hi : i≠783) :
    (routed (768,783) a).stacks i=a.stacks i := by simp [routed,hi]

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms

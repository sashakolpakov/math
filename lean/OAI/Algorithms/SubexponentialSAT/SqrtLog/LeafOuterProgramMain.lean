import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramMainState

namespace OAI.Algorithms

/-! The actual wide leaf as a reusable record callback. All parser transfers,
Main invocation, final answer pop, and reusable-work cleanup are paid here. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram.MainAdapter
open SubexponentialSAT BitProgram StructuredCalls SubexpMainProgram Execution

def callbackCost (coreCost : List Bool → ℕ) (nw Bw bits : List Bool) : ℕ :=
  100001*(bits.length+nw.length+Bw.length+coreCost bits+2)+5*bits.length+12

theorem body_contract (c : SubexponentialSAT.SubexpSetupProgram.Config) (hc : 896 < SubexponentialSAT.SubexpSetupProgram.helperSize c) (core : Cmd 40 896)
    (test : List Bool → Bool) (coreCost : List Bool → ℕ) (valid : List Bool → Prop)
    (nw Bw : List Bool) (hcore : CoreContract core test coreCost valid nw Bw) :
    LeafBodyContract (LeafMain.procedure c hc core) test (callbackCost coreCost nw Bw)
      (Invariant c hc nw Bw) valid := by
  intro bits tail base hv hb
  let a := transferredData (leafInput base tail bits)
  have af (i : Fin (totalStacks (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c)))
      (h7 : i≠persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 7)
      (h8 : i≠persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 8)
      (h9 : i≠persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 9) : a.stacks i=base.stacks i :=
    (transferred_stack_frame _ i h8 h9).trans (input_stack_frame _ _ _ i h7 h8)
  have aw : ∀ i, a.stacks (WideLeaf.stack c hc i)=[] := by
    intro i
    exact (af _ (WideLeaf.stack_ne_persistent c hc i 7)
      (WideLeaf.stack_ne_persistent c hc i 8)
      (WideLeaf.stack_ne_persistent c hc i 9)).trans (hb.work i)
  obtain ⟨a9,a8,a7⟩ := transfer_leafInput base tail bits hb.leaf
  have a10 : a.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 10)=[] :=
    (af _ (by simp) (by simp) (by simp)).trans hb.answer
  have a2 : a.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2)=nw :=
    (af _ (by simp) (by simp) (by simp)).trans hb.ambient
  have a24 : a.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24)=Bw :=
    (af _ (by simp) (by simp) (by simp)).trans hb.occurrence
  have ar := LeafMain.ready_of_blank c hc core a aw a10
  have ai := prepared_input c hc core a bits nw Bw ar a9 a2 a24
  obtain ⟨t,ht,b,he,hbit⟩ := hcore bits hv _ ai
  have wordBound := project_wordBound c hc core a bits nw Bw ar a9 a2 a24
  obtain ⟨total,out,hr,hcost,hout,hanswer,hwork,_,_⟩ :=
    LeafMain.procedure_bounded_eval c hc core a
      (bits.length+nw.length+Bw.length+1) wordBound ar he
  have outAnswer : out.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 10)=[test bits] :=
    hanswer.trans hbit
  have out9 : out.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 9)=bits := by
    rw [hout]
    exact (LeafMain.install_finished_sources c hc core a b 0).trans a9
  have out2 : out.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2)=nw := by
    rw [hout]
    exact (LeafMain.install_finished_sources c hc core a b 1).trans a2
  have out24 : out.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24)=Bw := by
    rw [hout]
    exact (LeafMain.install_finished_sources c hc core a b 2).trans a24
  have out7 : out.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 7)=tail := by
    rw [hout]
    exact (LeafMain.install_persistent_frame c hc core a _ 7
      (by intro i; fin_cases i <;> decide)).trans a7
  have out8 : out.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 8)=[] := by
    rw [hout]
    exact (LeafMain.install_persistent_frame c hc core a _ 8
      (by intro i; fin_cases i <;> decide)).trans a8
  refine ⟨⟨out,total,hr⟩,?_,?_,out7,out8,?_⟩
  · change transferCost (leafInput base tail bits)+(total+finishCost out) ≤ _
    rw [transfer_cost,finish_cost out bits (test bits) out9 outAnswer]
    unfold callbackCost
    omega
  · constructor
    · intro i
      exact (finished_stack_frame out _ (WideLeaf.stack_ne_persistent c hc i 9)
        (WideLeaf.stack_ne_persistent c hc i 10)).trans (hwork i)
    · exact finished_leaf out
    · exact finished_answer out
    · exact (finished_stack_frame out _ (by simp) (by simp)).trans out2
    · exact (finished_stack_frame out _ (by simp) (by simp)).trans out24
  · rw [outAnswer]
    rfl

theorem callback_contract (c : SubexponentialSAT.SubexpSetupProgram.Config) (hc : 896 < SubexponentialSAT.SubexpSetupProgram.helperSize c) (core : Cmd 40 896)
    (test : List Bool → Bool) (coreCost : List Bool → ℕ) (valid : List Bool → Prop)
    (nw Bw : List Bool) (hcore : CoreContract core test coreCost valid nw Bw) :
    RecordPrograms.CallbackContractOn (ports finalExtraRegisters (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c))
      (singleLeaf (LeafMain.procedure c hc core)) test (callbackCost coreCost nw Bw)
      (Invariant c hc nw Bw) valid :=
  singleLeaf_contract (body_contract c hc core test coreCost valid nw Bw hcore)

end SubexponentialSAT.SqrtLog.LeafOuterProgram.MainAdapter

end OAI.Algorithms

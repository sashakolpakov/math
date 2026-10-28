import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeRun

namespace OAI.Algorithms

/-! The closed per-node setup runs directly in the actual forty-register
leaf state, preserving branch registers and every external stack. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open BucketTupleProgram (enumerate)

abbrev project (a : State 40 768) : LeafHeadSetupProgram.Data :=
  projectState LeafHeadSetupProgram.wideRegisters id a

theorem wide_command_eval (s : Inputs) (a : State 40 768) (ha : Ready s (project a)) :
    ∃ ra rd rc words tables costs steps, ∃ e : State 40 768,
      CacheCorrect s.height (unary s.R) s.width words ∧
      ProducedHeads (start s (project a) ra rd rc words) s.n s.N s.D s.rows s.low
        s.relation s.columnLength (s.node.val*s.r) tables ∧
      tables.length=s.r ∧ costs.length=s.r ∧ Eval (.call wideProgram) steps a e ∧
      e.stacks 163=MomentsAssembly.bucketsInput
        (((enumerate tables).map (BucketTupleProgram.Representative.bucket s.n)).reverse) ∧
      (∀ i,External i→e.stacks i=a.stacks i) ∧
      (∀ i : Fin 768,640 ≤ i.val ∧ i.val < 680→e.stacks i=[]) ∧
      (∀ i : Fin 288,e.stacks (workPort (by decide) i)=[]) ∧
      e.stacks 710=words.flatten++a.stacks 710 ∧
      e.stacks 711=List.replicate (s.R*s.width.length) false++a.stacks 711 ∧
      e.stacks 712=s.power.1++a.stacks 712 ∧
      (∀ i : Fin 40,16 ≤ i.val→e.regs i=a.regs i) ∧
      (∃ loopEnd rf,
        CostTrace entry (start s (project a) ra rd rc words) s.n s.N s.D (s.Q*s.r) s.rows s.low
          s.relation s.columnTime s.columnLength (s.node.val*s.r) [[]] tables costs
          (start s (project a) ra rd rc words) loopEnd ∧
        e=embedState LeafHeadSetupProgram.wideRegisters id a
          (clearManyState cleanupPorts (finalResult loopEnd rf (unary s.n) (enumerate tables))) ∧
        steps ≤ nodeCost (project a) ra rd rc s.n s.r s.node.val s.records s.height (unary s.R)
          s.width words tables costs loopEnd rf+1 ∧
        loopEnd.stacks 660=BucketTupleProgram.Representative.tuplesBits (enumerate tables) ∧
        loopEnd.stacks 128=unary s.n) := by
  obtain ⟨ra,rd,rc,words,tables,costs,steps,b,hc,hp,ht,hcost,he,hout,hframe,hprivate,hwork,
    hpositive,hnegative,hdenominator,loopEnd,rf,htrace,hfinal,hbound,htuples,hn⟩ := command_eval s (project a) ha
  obtain ⟨hwide,hregs⟩ := wide_eval a b he
  have hstack (i : Fin 768) :
      (embedState LeafHeadSetupProgram.wideRegisters id a b).stacks i=b.stacks i :=
    embedState_stack LeafHeadSetupProgram.wideRegisters id a b Function.injective_id i
  refine ⟨ra,rd,rc,words,tables,costs,steps+1,_,hc,hp,ht,hcost,hwide,?_,?_,?_,?_,?_,?_,?_,hregs,?_⟩
  · exact (hstack 163).trans hout
  · intro i hi; exact (hstack i).trans (hframe i hi)
  · intro i hi; exact (hstack i).trans (hprivate i hi)
  · intro i; exact (hstack _).trans (hwork i)
  · exact (hstack 710).trans hpositive
  · exact (hstack 711).trans hnegative
  · exact (hstack 712).trans hdenominator
  · exact ⟨loopEnd,rf,htrace,by rw [hfinal],Nat.add_le_add_right hbound 1,htuples,hn⟩

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms

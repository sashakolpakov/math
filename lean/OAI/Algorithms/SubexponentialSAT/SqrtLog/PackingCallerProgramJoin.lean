import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramState

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

def compute : Wide.Code := .seq Wide.stage (Wide.bankCall coreProgram)
noncomputable def computeBudget (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) :=
  SubexponentialSAT.SubexpSetupStorage.copyManyCost Wide.stagePairs (Wide.project a)+1+
    coreBudget (Wide.parameterStore (Wide.project a)) p w tail

theorem compute_eval (a : Wide.Data) (p : Problem) (hs : Sources a p) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (hrows : (w::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q)
    (haN : (w::tail).Nodup) (haC : ∀ z,z∈w::tail) :
    ∃ t b, t ≤ computeBudget a p w tail ∧ Eval compute t a b ∧
      b.stacks=(middle a p w tail).stacks ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) := by
  obtain ⟨b,hb,hbs,hbr⟩ := Wide.stage_eval a he.temporary
  have hproj : projectState Wide.registers Wide.ports b=
      framed (Wide.parameterStore (Wide.project a))
        (Install.input (b.regs ∘ Wide.registers) p.scopes p.n p.mask) := by
    apply SubexponentialSAT.CounterForPrograms.data_ext
    · simp [projectState,Entry.install_eq]
    · have hh := congrArg StructuredProgram.State.stacks
        (Wide.staged_bank (Wide.project a) he.bank p.scopes p.n p.mask hs.scopes hs.ambientUnary hs.mask)
      funext i
      have hi := congrFun hh i
      simp only [projectState,framed_stack,Entry.install_eq] at hi ⊢
      simpa only [hbs] using hi
  obtain ⟨rf,nt,hnt,ht⟩ := core_run (Wide.parameterStore (Wide.project a)) p
    hs.parameters (parameters_workspace a) (b.regs ∘ Wide.registers) w tail hrows haN haC
  rw [← hproj] at ht
  have hc := Wide.bankCall_eval coreProgram b _ ht
  let e := embedState Wide.registers Wide.ports b
    (framed (outputStore (Wide.parameterStore (Wide.project a)) p w tail)
      (⟨rf,fun _=>[]⟩ : Small))
  refine ⟨_,e,by unfold computeBudget; omega,hb.seq hc,?_,?_⟩
  · funext i
    by_cases hi : 417 ≤ i.val ∧ i.val < 481
    · let j : Fin 64 := ⟨i.val-417,by omega⟩
      have hj : Wide.ports j=i := by apply Fin.ext; change 417+(i.val-417)=i.val; omega
      rw [← hj,middle_bank]
      change (embedState Wide.registers Wide.ports b _).stacks (Wide.ports j)=_
      rw [embedState_stack _ _ _ _ Wide.ports.injective]
      simp only [bankOutput,framed_stack]
    · have ho : i.val < 417 ∨ 481 ≤ i.val := by omega
      change (embedState Wide.registers Wide.ports b _).stacks i=_
      rw [Wide.bank_frame _ _ _ ho,middle_frame _ _ _ _ _ ho,hbs]
      exact Wide.staged_frame _ i ho
  · intro i hi
    exact (Wide.bank_register_frame b _ i hi).trans (hbr i hi)

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms

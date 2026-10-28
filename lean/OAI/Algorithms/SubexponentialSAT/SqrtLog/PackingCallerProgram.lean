import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramJoin
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramExportCost

namespace OAI.Algorithms

/-! A fixed per-query caller for actual native incidence construction, word
selection, layout metadata construction, and paid master-bank parking. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

def command : Wide.Code := .seq compute Wide.finish
def program := compiled command 718 735

noncomputable def result (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) : Wide.Local :=
  Wide.finished (middle a p w tail)

noncomputable def budget (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) :=
  computeBudget a p w tail+Wide.finishCost (middle a p w tail)+2

theorem command_eval (a : Wide.Data) (p : Problem) (hs : Sources a p) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (hrows : (w::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q)
    (haN : (w::tail).Nodup) (haC : ∀ z,z∈w::tail) :
    ∃ t b, t+1 ≤ budget a p w tail ∧ Eval command t a b ∧
      b.stacks=(result a p w tail).stacks ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) := by
  obtain ⟨tc,c,htc,hc,hcs,hcr⟩ := compute_eval a p hs he w tail hrows haN haC
  have ht : c.stacks 684=[] := by
    rw [hcs,middle_frame _ _ _ _ _ (by norm_num)]
    exact he.temporary
  obtain ⟨b,hf,hfs,hfr⟩ := Wide.finish_eval c ht
  have hcongr := Wide.finish_congr (Wide.project c) (middle a p w tail) hcs
  refine ⟨tc+(Wide.finishCost (Wide.project c)+1),b,?_,hc.seq hf,hfs.trans hcongr.1,?_⟩
  · unfold budget
    rw [hcongr.2]
    omega
  · intro i hi
    exact (hfr i hi).trans (hcr i hi)

theorem program_run (a : Wide.Data) (p : Problem) (hs : Sources a p) (he : Empty a) :
    ∃ w : Word p.r p.Q, ∃ tail : List (Word p.r p.Q), ∃ b : Wide.Data,
      (w::tail).Nodup ∧ (∀ z,z∈w::tail) ∧
      RunsIn program (budget a p w tail) (a.withPC (some program.entry)) (b.withPC none) ∧
      b.stacks=(result a p w tail).stacks ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) := by
  obtain ⟨w,tail,hrows,hn,hall⟩ := AssignmentAlphabetSemantics.wordBytes_order p.hr p.Q
  obtain ⟨t,b,ht,hc,hbs,hbr⟩ := command_eval a p hs he w tail hrows hn hall
  exact ⟨w,tail,b,hn,hall,⟨t+1,ht,compiled_halt_trace hc 718 735⟩,hbs,hbr⟩

theorem primitive_run (a : Wide.Data) (p : Problem) (hs : Sources a p) (he : Empty a) :
    ∃ w : Word p.r p.Q, ∃ tail : List (Word p.r p.Q), ∃ b : Wide.Data,
      (w::tail).Nodup ∧ (∀ z,z∈w::tail) ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program*budget a p w tail)
        (primitiveCfg program (a.withPC (some program.entry))) (primitiveCfg program (b.withPC none)) ∧
      b.stacks=(result a p w tail).stacks ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) := by
  obtain ⟨w,tail,b,hn,hall,h,hbs,hbr⟩ := program_run a p hs he
  exact ⟨w,tail,b,hn,hall,primitive_execution program h,hbs,hbr⟩

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms

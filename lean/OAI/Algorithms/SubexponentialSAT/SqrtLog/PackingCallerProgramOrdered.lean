import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramCost

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

/-- The quantified word alphabet is precisely the one physically emitted
by the loader, including its order and fixed-width serialization. -/
theorem ordered_run (a : Wide.Data) (p : Problem) (hs : Sources a p) (he : Empty a) :
    ∃ w : Word p.r p.Q, ∃ tail : List (Word p.r p.Q), ∃ b : Wide.Data,
      (w::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q ∧
      (w::tail).Nodup ∧ (∀ z,z∈w::tail) ∧
      RunsIn program (budget a p w tail) (a.withPC (some program.entry)) (b.withPC none) ∧
      b.stacks=(result a p w tail).stacks ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) := by
  obtain ⟨w,tail,hrows,hn,hall⟩ := AssignmentAlphabetSemantics.wordBytes_order p.hr p.Q
  obtain ⟨t,b,ht,hc,hbs,hbr⟩ := command_eval a p hs he w tail hrows hn hall
  exact ⟨w,tail,b,hrows,hn,hall,⟨t+1,ht,compiled_halt_trace hc 718 735⟩,hbs,hbr⟩

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms

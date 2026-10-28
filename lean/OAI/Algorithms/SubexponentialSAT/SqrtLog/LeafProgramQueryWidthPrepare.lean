import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQuerySetup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryPrepare

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Width
open SubexponentialSAT BitProgram StructuredCalls

theorem list_sum_lengths_le (a : Data) (U : ℕ) (h : ∀i,(a.stacks i).length ≤ U)
    (ps : List (Fin 768)) : (ps.map fun i=>(a.stacks i).length).sum ≤ ps.length*U := by
  induction ps with
  | nil => simp
  | cons i ps ih => simp only [List.map_cons,List.sum_cons,List.length_cons]; have := h i; nlinarith

def clearCoefficient : ℕ := 20+5*Count.Prepare.ports.length

theorem prepare_cost_le (a : Data) (U : ℕ) (h : ∀i,(a.stacks i).length ≤ U) :
    prepareCost a ≤ clearCoefficient*(U+1) := by
  have hs : ∀i,((Samples.prepared a).stacks i).length ≤ U := by
    intro i
    simp only [Samples.prepared_stacks,Function.update_apply]
    split_ifs <;> first | exact h i | simp
  have hsum := list_sum_lengths_le (Samples.prepared a) U hs Count.Prepare.ports
  have h190 := h 190
  have h191 := h 191
  have h699 := hs 699
  unfold prepareCost Samples.prepareCost Count.Prepare.budget clearCoefficient
  nlinarith

def incomingWidth {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : LeafParametersProgram.Guard (q.input k)} {W V L : ℕ}
    (p : Preparation q k a hg W V L) : ℕ :=
  W+p.frontSteps+p.packingSteps+p.arithmeticSteps+prepareCost p.out+
    (22*BinaryArithmetic.toNat q.ambient+43*((p.out.stacks 338).count true)+37)+
    (7*(p.out.stacks 338).length+5)

theorem output_mask {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : LeafParametersProgram.Guard (q.input k)} {W V L : ℕ}
    (p : Preparation q k a hg W V L) :
    p.out.stacks 338=LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) :=
  (p.arithmeticOutput.collectorFrame 338 (by decide) (by decide)).trans
    ((p.packingFrame 338 (by decide) (by decide) (by decide)).trans p.frontOutput.descending)

theorem prepared_mask {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : LeafParametersProgram.Guard (q.input k)} {W V L : ℕ}
    (p : Preparation q k a hg W V L) : (prepared p.out).stacks 338=p.out.stacks 338 :=
  (Count.Prepare.output_high_frame (Samples.prepared p.out) 338 (by decide) (by decide)).trans
    (Samples.prepared_frame p.out 338 (by decide) (by decide))

theorem incomingWidth_le {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : LeafParametersProgram.Guard (q.input k)} {W V L : ℕ}
    (p : Preparation q k a hg W V L) (hw : ∀i,(a.stacks i).length ≤ W) :
    incomingWidth p ≤
      (clearCoefficient+51)*(W+p.frontSteps+p.packingSteps+p.arithmeticSteps+1)+
        22*BinaryArithmetic.toNat q.ambient+42 := by
  have hp := p.output_width hw
  have hc := prepare_cost_le p.out _ hp
  have hm := hp 338
  have hcount : (p.out.stacks 338).count true ≤ (p.out.stacks 338).length := List.count_le_length
  unfold incomingWidth
  nlinarith

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Width

end OAI.Algorithms

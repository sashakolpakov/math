import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeCount
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeSamples

namespace OAI.Algorithms

/-! Every stage of the residual query is included in this explicit bound. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native
open SubexponentialSAT BitProgram StructuredCalls

 def preparationBound (W : ℕ) : ℕ :=
  (2*Count.Prepare.ports.length+2)*W+3*Count.Prepare.ports.length+6

 theorem lengths_sum_le (a : Data) (is : List (Fin 768)) (W : ℕ)
    (hw : ∀ i,(a.stacks i).length ≤ W) :
    (is.map (fun i => (a.stacks i).length)).sum ≤ is.length*W := by
  induction is with
  | nil => simp
  | cons i is ih =>
    have hi := hw i
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

 theorem preparation_bound (a : Data) (W : ℕ)
    (hw : ∀ i,(a.stacks i).length ≤ W) : Count.Prepare.budget a ≤ preparationBound W := by
  have h := lengths_sum_le a Count.Prepare.ports W hw
  have h699 := hw 699
  unfold Count.Prepare.budget preparationBound
  nlinarith

 theorem tail_bound (a : Data) (r : Recovery a) (W C : ℕ)
    (hw : ∀ i,(a.stacks i).length ≤ W) (hc : r.cost ≤ C) :
    tailBudget a r ≤ preparationBound W+C+6*W+9 := by
  have hp := preparation_bound a W hw
  have h265 := hw 265
  have h702 := hw 702
  have h703 := hw 703
  unfold tailBudget
  omega

 def highBound (a : Data) (h : ℕ) : ℕ := 22*(a.stacks 338).length+43*h+37

 def residualBound (W H S C : ℕ) : ℕ :=
  H+S+preparationBound (W+H+S)+C+6*(W+H+S)+9

 theorem sampleBudget_high (a : Data) (regs : Fin 4 → Bool) (high : List Bool)
    (nodes : ℕ → List Bool) (cost : ℕ → ℕ) (maxJet Q : ℕ) :
    sampleBudget (LeafHighContextProgram.finished a regs high) nodes cost maxJet Q=
      sampleBudget a nodes cost maxJet Q := by
  have hf (i : Fin 768) (hi : i∉LeafHighContextProgram.changed) :=
    LeafHighContextProgram.finished_frame a regs high i hi
  have h190 := hf 190 (by decide)
  have h191 := hf 191 (by decide)
  have h256 := hf 256 (by decide)
  simp only [sampleBudget,Samples.prepareCost,
    Samples.prepared_frame _ 256 (by decide) (by decide),h190,h191,h256]

 theorem sampleBudget_uniform (a : Data) (nodes : ℕ → List Bool) (cost : ℕ → ℕ)
    (maxJet Q N K : ℕ)
    (hn : ∀ i < Q,(nodes i).length ≤ N) (hc : ∀ i < Q,cost i ≤ K) :
    sampleBudget a nodes cost maxJet Q ≤ Samples.prepareCost a+
      Q*(K+33*N+6*maxJet+38)+2*(a.stacks 256).length+27 := by
  have h := LeafNodeSamplesProgram.Rel.collectBound_le nodes cost maxJet Q N K
    ((Samples.prepared a).stacks 256) hn hc
  rw [Samples.prepared_frame a 256 (by decide) (by decide)] at h
  unfold sampleBudget
  rw [Samples.prepared_frame a 256 (by decide) (by decide)]
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native

end OAI.Algorithms

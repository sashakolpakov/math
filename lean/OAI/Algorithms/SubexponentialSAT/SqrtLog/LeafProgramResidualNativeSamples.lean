import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgramRelWitness

namespace OAI.Algorithms

/-! Adapt the relational collector's exact Store endpoint to the actual
Samples command. The native-node contract is discharged separately. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native
open SubexponentialSAT BitProgram StructuredCalls
open LeafNodeSamplesProgram
universe u

noncomputable section

def sampled (a : Data) (nodes : ℕ → List Bool) {Q : ℕ}
    (jets : Fin Q → List Bool) (regs : Fin 40 → Bool) : Data :=
  state regs (Rel.finishedIndexed (Samples.prepared a).stacks nodes jets)

def sampleBudget (a : Data) (nodes : ℕ → List Bool) (cost : ℕ → ℕ)
    (maxJet Q : ℕ) : ℕ :=
  Samples.prepareCost a+
    Rel.collectBound nodes cost maxJet ((Samples.prepared a).stacks 256) Q+1

/-- This adapter retains the collector's intermediate native-worker
obligation; it does not replace the closed node theorem. -/
theorem samples_of_contract (Valid : (Fin 768 → List Bool) → Prop)
    (nodes : ℕ → List Bool) (Entry : ℕ → Type u)
    (encode : (i : ℕ) → Entry i → List Bool)
    (ValidEntry : (i : ℕ) → Entry i → Prop)
    (cost : ℕ → ℕ) (maxJet Q : ℕ)
    (hc : Rel.WorkerContract Node.command Valid nodes
      (Rel.WitnessResult Entry encode ValidEntry) cost maxJet Q)
    (a : Data) (hv : Valid (Samples.prepared a).stacks)
    (he : ∀ i∈collectorBlankPorts,(Samples.prepared a).stacks i=[])
    (hs : (Samples.prepared a).stacks 300=
      Encoding.encodeList id (records (Rel.nodeSamples nodes) 0 Q)) :
    ∃ entries : (i : Fin Q) → Entry i.val,
      (∀ i,ValidEntry i.val (entries i) ∧ (encode i.val (entries i)).length ≤ maxJet) ∧
      ∃ time regs, time ≤ sampleBudget a nodes cost maxJet Q ∧
        Eval Samples.command time a (sampled a nodes (fun i => encode i.val (entries i)) regs) ∧
        RegFrame a.regs regs := by
  obtain ⟨entries,hh,k,hk,regs,hr,hc⟩ := Rel.collect_eval_witness Node.command Valid nodes
    Entry encode ValidEntry cost maxJet Q hc (Samples.prepared a).stacks
    ((Samples.prepared a).stacks 256) (Samples.prepared a).regs hv hs
  rw [collector_initial (Samples.prepared a) he] at hc
  have ht := compiled_halt_trace hc 300 265
  refine ⟨entries,hh,Samples.prepareCost a+(k+1),regs,?_,
    (Samples.prepare_eval a).seq (Eval.call _ ht),?_⟩
  · unfold sampleBudget
    omega
  · intro i hlo hhi
    exact (hr i hlo hhi).trans (samples_prepared_register a i (by omega))

theorem sampled_protected (a : Data) (nodes : ℕ → List Bool) {Q : ℕ}
    (jets : Fin Q → List Bool) (regs : Fin 40 → Bool)
    (i : Fin 768) (hi : Query.Protected i) :
    (sampled a nodes jets regs).stacks i=a.stacks i := by
  exact (collector_frame _ i (protected_collector i hi)).trans
    (samples_prepared_protected a i hi)

theorem sampled_nodes (a : Data) (nodes : ℕ → List Bool) {Q : ℕ}
    (jets : Fin Q → List Bool) (regs : Fin 40 → Bool) :
    (sampled a nodes jets regs).stacks 256=
      ((List.finRange Q).map (fun i => nodes i.val)).flatten := by
  simp only [sampled,state,tapes_nodesOut,Rel.finishedIndexed]

theorem sampled_jets (a : Data) (nodes : ℕ → List Bool) {Q : ℕ}
    (jets : Fin Q → List Bool) (regs : Fin 40 → Bool) :
    (sampled a nodes jets regs).stacks 265=((List.finRange Q).map jets).flatten := by
  simp only [sampled,state,tapes_jetsOut,Rel.finishedIndexed]

end
end SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native

end OAI.Algorithms

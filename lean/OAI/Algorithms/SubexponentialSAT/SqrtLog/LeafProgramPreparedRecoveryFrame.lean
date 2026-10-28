import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedRecoveryBase
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchFrame

namespace OAI.Algorithms

/-! Actual query preparation and the branch frame preserve every physical
ring input needed by the reconstruction factory, including exponent tape209. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedRecovery
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
open Residual.Native
attribute [local simp] Fin.coe_ofNat_eq_mod
noncomputable section

private theorem ring_safe (i : Fin 320) (hi : i∈ringPorts) :
    Count.crtStacks i∉collectorPorts ∧ Count.crtStacks i≠190 ∧ Count.crtStacks i≠191 ∧
    Count.crtStacks i∉LeafHighContextProgram.changed ∧ ¬outerTape (Count.crtStacks i) ∧
    Count.crtStacks i∉Residual.Branch.mutable ∧ Count.crtStacks i≠333 ∧
    Count.crtStacks i∉Count.Prepare.ports ∧ Count.crtStacks i≠699 := by
  simp only [ringPorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [Count.crtStacks, collectorPorts, LeafHighContextProgram.changed,
      outerTape, Residual.Branch.mutable]
  all_goals
    apply Count.Prepare.protected_not_mem
    simp [Count.Prepare.protectedInputs]

variable {q : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Query.Preparation q k initial hg W V L)

 theorem query_ringFrame : RingFrame p.ringState p.out := by
  intro i hi
  exact p.arithmeticOutput.low (i.castAdd 320) (by change i.val < 340; omega)

 theorem sampled_ringFrame (a : Factor.Data)
    (ha : Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a)
    (rh : Fin 4 → Bool) (high : List Bool) (nodes : ℕ → List Bool) {Q : ℕ}
    (jets : Fin Q → List Bool) (rr : Fin 40 → Bool) :
    RingFrame p.ringState (sampled (LeafHighContextProgram.finished (outerReference a) rh high) nodes jets rr) := by
  intro i hi
  obtain ⟨hc,h190,h191,hh,ho,hmut,h333,hprep,h699⟩ := ring_safe i hi
  change LeafNodeSamplesProgram.tapes _ (Count.crtStacks i)=_
  rw [collector_frame _ _ hc]
  change (Samples.prepared (LeafHighContextProgram.finished (outerReference a) rh high)).stacks (Count.crtStacks i)=_
  rw [Samples.prepared_frame _ _ h190 h191,
    LeafHighContextProgram.finished_frame _ _ _ _ hh,
    outerReference_visible _ _ ho,ha.2 _ hmut,Marked.Wide.maskCopied_frame _ _ h333]
  change (Count.Prepare.output (Samples.prepared p.out)).stacks (Count.crtStacks i)=_
  rw [Count.Prepare.output_frame _ _ hprep h699,Samples.prepared_frame _ _ h190 h191]
  exact query_ringFrame p i hi

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedRecovery

end OAI.Algorithms

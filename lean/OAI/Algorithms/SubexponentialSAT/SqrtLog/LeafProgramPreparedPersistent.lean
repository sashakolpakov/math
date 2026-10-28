import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PreparedNodeReadyFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeMask

namespace OAI.Algorithms

/-! The actual query, branch, and collector state maps retain the ring,
interpolation, source, and selector master tapes used by the factor program. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def persistentPorts : List (Fin 768) :=
  [194,201,202,203,204,207,211,212,243,280,281,
   700,701,704,705,706,707,708,709,713,714,715,716,717,728]

def Persistent (base a : Factor.Data) : Prop :=
  ∀ i∈persistentPorts,a.stacks i=base.stacks i

private theorem persistent_conditions (i : Fin 768) (hi : i∈persistentPorts) :
    i≠190 ∧ i≠191 ∧ i≠699 ∧ i≠333 ∧ i≠330 ∧
    i∉Count.Prepare.ports ∧ i∉LeafHighContextProgram.changed ∧
    i∉NodeNative.carriedPorts ∧ i≠307 ∧ i≠78 ∧ i≠102 ∧ i≠104 ∧
    i∉Node.cleanupPorts := by
  simp only [persistentPorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [Count.Prepare.ports_not_mem_of_ge, LeafHighContextProgram.changed,
      NodeNative.carriedPorts, Node.mem_cleanup]
  all_goals
    apply Count.Prepare.protected_not_mem
    simp [Count.Prepare.protectedInputs]

 theorem Persistent.refl (base : Factor.Data) : Persistent base base := fun _ _=>rfl
 theorem Persistent.trans {a b c : Factor.Data} (h : Persistent a b) (g : Persistent b c) :
    Persistent a c := fun i hi=>(g i hi).trans (h i hi)

 theorem persistent_prepared (a : Factor.Data) : Persistent a (Query.prepared a) := by
  intro i hi
  obtain ⟨h190,h191,h699,_,_,hc,_⟩ := persistent_conditions i hi
  exact (Count.Prepare.output_frame _ i hc h699).trans (Samples.prepared_frame a i h190 h191)

 theorem persistent_maskCopied (a : Factor.Data) : Persistent a (Marked.Wide.maskCopied a) := by
  intro i hi
  exact Marked.Wide.maskCopied_frame a i (persistent_conditions i hi).2.2.2.1

 theorem persistent_counter (a : Factor.Data) (bits : List Bool) :
    Persistent a ⟨a.regs,Function.update a.stacks 330 bits⟩ := by
  intro i hi
  exact Function.update_of_ne (persistent_conditions i hi).2.2.2.2.1 _ _

 theorem persistent_highContext (a : Factor.Data) (regs : Fin 4 → Bool) (high : List Bool) :
    Persistent a (LeafHighContextProgram.finished a regs high) := by
  intro i hi
  exact LeafHighContextProgram.finished_frame a regs high i (persistent_conditions i hi).2.2.2.2.2.2.1

 theorem persistent_collector (store : LeafNodeSamplesProgram.Store) (regs : Fin 40 → Bool) :
    Persistent ⟨regs,store.frame⟩ (LeafNodeSamplesProgram.state regs store) := by
  intro i hi
  obtain ⟨_,_,_,_,_,_,_,hc,h307,h78,h102,h104,_⟩ := persistent_conditions i hi
  have h := hc
  simp only [NodeNative.carriedPorts,List.mem_cons,List.mem_nil_iff,or_false,not_or] at h
  simp only [LeafNodeSamplesProgram.state,LeafNodeSamplesProgram.tapes,
    ite_eq_right h.2.2.1,ite_eq_right h.2.2.2.1,ite_eq_right h.2.2.2.2.1,ite_eq_right h.2.2.2.2.2.1,
    ite_eq_right h.2.2.2.2.2.2,ite_eq_right h307,ite_eq_right h78,ite_eq_right h102,ite_eq_right h104,ite_eq_right h.1,ite_eq_right h.2.1]

 theorem persistent_maskStore (store : LeafNodeSamplesProgram.Store) (regs : Fin 40 → Bool) :
    Persistent (LeafNodeSamplesProgram.state regs store)
      (LeafNodeSamplesProgram.state regs (Residual.Native.maskStore store)) := by
  intro i hi
  exact (Residual.Native.maskStore_tapes store i).trans
    (ite_eq_right (persistent_conditions i hi).2.2.2.2.2.2.2.1)

 theorem persistent_node {s : NodeNative.HeadInputs} {a b : Factor.Data}
    (p : NodeNative.Preparation s a b) : Persistent a b := by
  intro i hi
  exact p.frame i (persistent_conditions i hi).2.2.2.2.2.2.2.2.2.2.2.2

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentRegisterFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeWide
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram

namespace OAI.Algorithms

/-! Exact public frames for the concrete node worker. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeNative
open SubexponentialSAT BitProgram StructuredCalls
open MomentsAssembly.RegisterFrame
attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 40 768

/-- Reusable node storage is blank; the current node itself is supplied at78. -/
def Blank (a : Data) : Prop :=
  ∀ i ∈ Node.cleanupPorts, i ≠ 78 → a.stacks i=[]

theorem low_mem_cleanup (i : Fin 14) : LayoutMasters.low i ∈ Node.cleanupPorts := by
  apply (Node.mem_cleanup _).mpr
  left
  change 128+i.val < 142 ∧ 128+i.val ≠ 102
  have := i.isLt
  omega

theorem not_cleanup_not_low {i : Fin 768} (hi : i ∉ Node.cleanupPorts) :
    i ∉ LayoutMasters.lowPorts := by
  intro hm
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hm
  exact hi (low_mem_cleanup j)

theorem not_cleanup_head_external {i : Fin 768} (hi : i ∉ Node.cleanupPorts) :
    LeafHeadSetupProgram.External i := by
  have h := mt (Node.mem_cleanup i).mpr hi
  have h163 : i ≠ 163 := by intro he; subst i; norm_num at h
  have h710 : i ≠ 710 := by intro he; subst i; norm_num at h
  have h711 : i ≠ 711 := by intro he; subst i; norm_num at h
  have h712 : i ≠ 712 := by intro he; subst i; norm_num at h
  refine ⟨?_,h163,h710,h711,h712⟩
  omega

theorem cache_mem_cleanup {i : Fin 768} (hi : i ∈ LeafNodeCacheProgram.cachePorts) :
    i ∈ Node.cleanupPorts := by
  simp only [LeafNodeCacheProgram.cachePorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    apply (Node.mem_cleanup _).mpr <;> norm_num

theorem cache_not_low {i : Fin 768} (hi : i ∈ LeafNodeCacheProgram.cachePorts) :
    i ∉ LayoutMasters.lowPorts := by
  intro hm
  obtain ⟨j,_,hj⟩ := List.mem_map.mp hm
  have hv := congrArg Fin.val hj
  change 128+j.val=i.val at hv
  simp only [LeafNodeCacheProgram.cachePorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num at hv <;> have := j.isLt <;> omega

theorem clearList_register (is : List (Fin 768)) (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves (Node.clearList is) i := by
  induction is with
  | nil => exact LeafAssignmentRegisterFrame.skip i
  | cons j js ih =>
    exact fun {n} {a} {b} => seq (MomentsAssembly.RegisterFrame.clear j i hi) ih

theorem cleanup_register {k : ℕ} {a b : Data} (he : Eval Node.cleanup k a b)
    (i : Fin 40) (hi : 16 ≤ i.val) : b.regs i=a.regs i :=
  clearList_register Node.cleanupPorts i hi he

theorem cleaned_register (a : Data) (i : Fin 40) (hi : 16 ≤ i.val) :
    (Node.cleaned a).regs i=a.regs i := cleanup_register (Node.cleanup_eval a) i hi

/-- The exact node output state is the collector's existing record update. -/
theorem collector_output (regs : Fin 40 → Bool) (s : LeafNodeSamplesProgram.Store)
    (bits : List Bool) (hshape : s.shape=[]) :
    (⟨regs,Function.update (Function.update (LeafNodeSamplesProgram.tapes s) 78 []) 102 bits⟩ : Data)=
      LeafNodeSamplesProgram.state regs {s with node:=[],jet:=bits,shape:=[]} := by
  apply congrArg (StructuredProgram.State.mk regs)
  rw [LeafNodeSamplesProgram.update_node,LeafNodeSamplesProgram.update_jet]
  funext i
  simp only [LeafNodeSamplesProgram.tapes,hshape]

end SubexponentialSAT.SqrtLog.LeafProgram.NodeNative

end OAI.Algorithms

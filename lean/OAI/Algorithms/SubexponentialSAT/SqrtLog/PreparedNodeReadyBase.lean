import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativePrepare

namespace OAI.Algorithms

/-! Physical parked-word readiness for the fixed node loader. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady
open SubexponentialSAT BitProgram StructuredCalls LeafHeadSetupProgram
attribute [local simp] Fin.coe_ofNat_eq_mod
abbrev Data := State 40 768

private theorem lowPorts_660 : (660 : Fin 768) ∉ LayoutMasters.lowPorts := by
  intro h
  obtain ⟨i, _, hi⟩ := List.mem_map.mp h
  have hv := congrArg Fin.val hi
  simp [LayoutMasters.low] at hv
  omega

private theorem lowPorts_665 : (665 : Fin 768) ∉ LayoutMasters.lowPorts := by
  intro h
  obtain ⟨i, _, hi⟩ := List.mem_map.mp h
  have hv := congrArg Fin.val hi
  simp [LayoutMasters.low] at hv
  omega

private theorem cleanupPorts_660 : (660 : Fin 768) ∈ Node.cleanupPorts := by
  apply (Node.mem_cleanup _).mpr
  norm_num

private theorem cleanupPorts_665 : (665 : Fin 768) ∈ Node.cleanupPorts := by
  apply (Node.mem_cleanup _).mpr
  norm_num

structure Parked (s : Native.Inputs) (a : Data) : Prop where
  ambient : a.stacks 730=unary s.n
  factors : a.stacks 731=unary s.N
  colors : a.stacks 732=unary s.r
  nodes : a.stacks 733=unary s.Q
  wordWidth : a.stacks 734=unary (s.Q*s.r)
  words : a.stacks 735=s.rows.flatten
  low : a.stacks 736=s.low
  metadata : a.stacks 737=s.metadata
  plans : a.stacks 738=LayoutOwnerFiberProgram.stream s.plans
  order : a.stacks 740=unary s.R
  height : a.stacks 741=s.height
  width : a.stacks 742=s.width
  offset : BinaryArithmetic.toNat (a.stacks 743)=s.offset

theorem Parked.congr {s : Native.Inputs} {a b : Data} (h : Parked s a)
    (hf : ∀ i : Fin 768,730 ≤ i.val → i.val < 744 → b.stacks i=a.stacks i) : Parked s b := by
  constructor
  all_goals first
    | exact (hf _ (by decide) (by decide)).trans h.ambient
    | exact (hf _ (by decide) (by decide)).trans h.factors
    | exact (hf _ (by decide) (by decide)).trans h.colors
    | exact (hf _ (by decide) (by decide)).trans h.nodes
    | exact (hf _ (by decide) (by decide)).trans h.wordWidth
    | exact (hf _ (by decide) (by decide)).trans h.words
    | exact (hf _ (by decide) (by decide)).trans h.low
    | exact (hf _ (by decide) (by decide)).trans h.metadata
    | exact (hf _ (by decide) (by decide)).trans h.plans
    | exact (hf _ (by decide) (by decide)).trans h.order
    | exact (hf _ (by decide) (by decide)).trans h.height
    | exact (hf _ (by decide) (by decide)).trans h.width
    | exact (congrArg BinaryArithmetic.toNat (hf _ (by decide) (by decide))).trans h.offset

theorem Parked.ready {s : Native.Inputs} {a : Data} (h : Parked s a)
    (hb : NodeNative.Blank a) (hn : a.stacks 307=unary s.node.val) : NodeNative.Ready s a := by
  have hl (i : Fin 14) : (NodeNative.loadedState a).stacks (LayoutMasters.low i)=
      a.stacks (LayoutMasters.high i) :=
    LayoutMasters.loaded_low (LayoutMasters.project a)
      (fun j=>hb _ (NodeNative.low_mem_cleanup j) (by
        intro he; have hv := congrArg Fin.val he
        change 128+j.val=78 at hv
        omega)) i
  have hf (i : Fin 768) (hi : i∉LayoutMasters.lowPorts) :
      (NodeNative.loadedState a).stacks i=a.stacks i :=
    LayoutMasters.loaded_frame (LayoutMasters.project a) i hi
  refine ⟨hb,?_⟩
  constructor
  · exact (hl 0).trans h.ambient
  · exact (hl 1).trans h.factors
  · exact (hl 2).trans h.colors
  · exact (hl 3).trans h.nodes
  · exact (hl 4).trans h.wordWidth
  · exact (hl 5).trans h.words
  · exact (hl 6).trans h.low
  · exact (hl 7).trans h.metadata
  · exact (hl 8).trans h.plans
  · exact (hl 10).trans h.order
  · exact (hl 11).trans h.height
  · exact (hl 12).trans h.width
  · exact (congrArg BinaryArithmetic.toNat (hl 13)).trans h.offset
  · exact (hf 307 (by decide)).trans hn
  · exact (hf 660 lowPorts_660).trans (hb 660 cleanupPorts_660 (by decide))
  · exact (hf 665 lowPorts_665).trans (hb 665 cleanupPorts_665 (by decide))
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady

end

end OAI.Algorithms

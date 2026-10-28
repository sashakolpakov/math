import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyAssignment
import OAI.Algorithms.SubexponentialSAT.SqrtLog.FactorResourceReady
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgramBounds

namespace OAI.Algorithms

/-! Retained physical row-width and metadata words discharge source caps;
no product-of-dimensions assumption is left to the caller. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open MomentsAssembly MomentsProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

 theorem source_bounds {r Q n d A : ℕ} {q : Factor.Spec r Q n d}
    {high : Fin 768 → List Bool} (h : NodeFacts q high)
    (hs : NodeEnvelope.AssignmentStorage q (List.replicate d true) A high)
    (hRQ : q.p.R+1 ≤ Q) :
    (q.p.R+1)*(d*baseWidth 3 q.p.t) ≤ A ∧ q.p.R+1 ≤ A ∧
      (∀ x,SourceBank.MetadataBound (PackingMetadata.value q.packing CollisionProgram.encodeType x) A) ∧
      q.ps.length ≤ A := by
  have hf := assignment_fixed q (List.replicate d true) high
  have hcap (i : Fin 768) (hi : 56 ≤ i.val)
      (he : i∉([145,146,147,148] : List (Fin 768))) (hc : ¬FactorLoop.collectorTape i) :
      (high i).length ≤ A := by
    rw [←hf i hi he hc]
    exact hs.1 i
  have hrow := hcap 716 (by decide) (by decide) (by decide)
  have he716 : high 716=q.p.rowWidth := h.source.rowWidth
  rw [he716,q.p.hrowWidth,q.p.hringWidth] at hrow
  have hnodes := hcap 131 (by decide) (by decide) (by decide)
  have he131 : high 131=List.replicate Q true := h.source.nodes
  rw [he131,List.length_replicate] at hnodes
  have hmetadata := hcap 135 (by decide) (by decide) (by decide)
  change ((FactorReady.baseData high).stacks 135).length ≤ A at hmetadata
  rw [h.source.metadata] at hmetadata
  have hplans := hcap 136 (by decide) (by decide) (by decide)
  change ((FactorReady.baseData high).stacks 136).length ≤ A at hplans
  rw [h.source.plans,LayoutOwnerFiberProgram.stream_length] at hplans
  refine ⟨(Nat.mul_le_mul_right _ hRQ).trans hrow,hRQ.trans hnodes,?_,by omega⟩
  intro x
  have hinj : Function.Injective (fun v : Fin q.ps.length=>List.replicate v.val true) := by
    intro x y he; apply Fin.ext; simpa using congrArg List.length he
  have hl := PackingMetadata.lookup_eq q.packing (fun v=>List.replicate v.val true)
    CollisionProgram.encodeType hinj x
  have hp := (GlobalBasisMetadata.payload_length_le _ _ _ hl).trans hmetadata
  have hb (m : GlobalBasisMetadata.Metadata) :
      m.block.length ≤ m.encode.length ∧ m.typeCode.length ≤ m.encode.length ∧ m.rank.length ≤ m.encode.length := by
    cases m <;> simp [GlobalBasisMetadata.Metadata.block,GlobalBasisMetadata.Metadata.typeCode,
      GlobalBasisMetadata.Metadata.rank,GlobalBasisMetadata.Metadata.encode,Encoding.length_frame] <;> omega
  exact ⟨(hb _).1.trans hp,(hb _).2.1.trans hp,(hb _).2.2.trans hp⟩

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms

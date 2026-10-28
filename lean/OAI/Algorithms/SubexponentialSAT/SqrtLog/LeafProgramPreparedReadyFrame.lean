import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadySource

namespace OAI.Algorithms

/-! The actual assignment setup changes only its explicit low/saved ports;
collector masking is a proof-only operation on disjoint tapes. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls MomentsProgram MomentsAssembly
open SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native IdempotentApplyProgram.Steps
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q n d : ℕ} (q : Factor.Spec r Q n d) (degree : List Bool)

noncomputable def assignmentBase (high : Fin 768 → List Bool) : Fin 768 → List Bool :=
  FactorLoop.preparedAssignment q degree (FactorLoop.maskedHigh high) [] []

theorem assignment_fixed (high : Fin 768 → List Bool) (i : Fin 768)
    (hi : 56 ≤ i.val) (hs : i∉([145,146,147,148] : List (Fin 768)))
    (hc : ¬FactorLoop.collectorTape i) : assignmentBase q degree high i=high i := by
  simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at hs
  unfold assignmentBase FactorLoop.preparedAssignment
  rw [LeafAssignmentSetupProgram.prepared_stack_frame]
  · unfold FactorLoop.assignmentMachine machine
    simp only [show ¬ i.val < 56 by omega, ↓reduceDIte]
    exact FactorLoop.masked_at high i hc
  · simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or]
    exact ⟨by intro he; subst i; norm_num at hi,
      by intro he; subst i; norm_num at hi,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2⟩

theorem assignment_low (high : Fin 768 → List Bool) (hdegree : degree=List.replicate d true) :
    ∀ i : Fin 56,assignmentBase q degree high (Factor.nativeStacks (Memory.lowPort i))=low q.ctx i := by
  subst degree
  intro i
  fin_cases i <;>
    simp [assignmentBase,FactorLoop.preparedAssignment,LeafAssignmentSetupProgram.prepared_stacks,
      FactorLoop.assignmentMachine,FactorLoop.assignmentEnvironment,machine,Product.working,
      Product.environment,Product.idle,Product.tapes,Normalize.bytes,
      Squarefree.Program.rawEntries,Squarefree.Program.encodeDictionary,Factor.nativeStacks,
      Memory.lowPort,low,Factor.Spec.ctx,Factor.sourceContext]

theorem assignment_choices (high : Fin 768 → List Bool) :
    (assignmentBase q degree high 145).length=(high 174).length := by
  simp [assignmentBase,FactorLoop.preparedAssignment,LeafAssignmentSetupProgram.prepared_stacks,
    FactorLoop.assignmentMachine,machine,FactorLoop.masked_at high 174 (by decide),
    FactorLoop.masked_at high 178 (by decide),FactorLoop.masked_at high 177 (by decide),
    LeafAssignmentMergeProgram.merge_length]

private def sourcePorts : List (Fin 768) :=
  [130,131,132,710,711,140,712,138,139,135,136,713,714,715,717,716,280,207,211,728]

private theorem assignment_source_fixed (high : Fin 768 → List Bool) :
    ∀ i ∈ sourcePorts, assignmentBase q degree high i = high i := by
  intro i hi
  simp only [sourcePorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    apply assignment_fixed q degree high <;> decide

attribute [local irreducible] assignmentBase


theorem source_masters_assignment {ps : List (ℕ × ℕ)}
    {P : SubexponentialSAT.Subexp.ConstructivePacking.PackingData (Fin ps.length)
      (SubexponentialSAT.MulticolorTypes.UniversalType r Q 1)}
    (high : Fin 768 → List Bool)
    (h : SourceMasters q.p ps P (FactorReady.baseData high)) :
    SourceMasters q.p ps P (FactorReady.baseData (assignmentBase q degree high)) := by
  have hf := assignment_source_fixed q degree high
  constructor
  · exact (hf 130 (by decide)).trans h.colors
  · exact (hf 131 (by decide)).trans h.nodes
  · exact (hf 132 (by decide)).trans h.typeWidth
  · exact (hf 710 (by decide)).trans h.positive
  · exact (hf 711 (by decide)).trans h.negative
  · exact (hf 140 (by decide)).trans h.scalarWidth
  · exact (hf 712 (by decide)).trans h.power
  · exact h.powerNegative
  · exact (hf 138 (by decide)).trans h.radius
  · exact (hf 139 (by decide)).trans h.offset
  · exact (hf 135 (by decide)).trans h.metadata
  · exact (hf 136 (by decide)).trans h.plans
  · exact (hf 713 (by decide)).trans h.inverses
  · exact (hf 714 (by decide)).trans h.negatives
  · exact (hf 715 (by decide)).trans h.differences
  · exact (hf 717 (by decide)).trans h.ringWidth
  · exact (hf 716 (by decide)).trans h.rowWidth
  · exact (hf 280 (by decide)).trans h.zero
  · exact (hf 207 (by decide)).trans h.one
  · exact (hf 211 (by decide)).trans h.minusOne
  · exact (hf 728 (by decide)).trans h.inverseDenominator

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms

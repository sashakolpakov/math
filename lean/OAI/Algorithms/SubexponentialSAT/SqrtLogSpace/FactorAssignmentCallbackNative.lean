import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorSpec
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorJet
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentConcrete
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSelected

/-! Concrete physical inputs for the streamed factor callback. The source
context is the actual q.ctx, and the dispatcher determines every selected row
and clause. These predicates contain stored words and finite size bounds only.
Their construction from the actual loader/cache run remains an integration step. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram

noncomputable section

/-- Exact selected-payload state produced by the concrete dispatcher. -/
def fetched {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (a : FactorAssignmentProgram.Data) (f : ℕ) (rf : Fin 8 → Bool) :
    FactorAssignmentProgram.Data := dispatched a rf q.rawRows q.clauses q.marked q.mark f

/-- Physical callback boundary, specialized to the source's actual arithmetic
context. In particular no incidence family or evaluator execution is a field. -/
structure Input {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A S : ℕ)
    (one seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (a : FactorAssignmentProgram.Data) (f : ℕ) : Prop where
  scalar : FactorTableNative.ScalarMasters q.p.t q.p.model q.p.modulus q.p.cache q.J q.p.R
    q.theta (projectState localRegister FactorTableProgram.basePort a) n
  masters : FactorTableNative.SourceMasters q.p q.ps q.packing
    (projectState localRegister FactorTableProgram.basePort a)
  incoming : ∀ i, (a.stacks i).length ≤ A
  size : 1029*A+99+n+n*FactorTableProgram.literalRecordBound n
    (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1 ≤ S
  radius : q.p.R+1 ≤ Q
  rows : a.stacks 701 = Encoding.encodeList id q.rawRows
  clauses : a.stacks 700 = Encoding.encodeList id q.clauses
  count : a.stacks 704 = List.replicate q.rawRows.length true
  mark : a.stacks 705 = Encoding.encodeNat q.mark
  flag : a.stacks 706 = [q.marked]
  factor : a.stacks 149 = (Encoding.encodeNat f).reverse
  seedBytes : a.stacks 151 = Product.bytes seed
  blank : ∀ i ∈ callbackScratch, a.stacks (lowStack i) = []
  tableBlank : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 → a.stacks i = []
  correction : (a.stacks 857).length = n
  hashWidth : (a.stacks 708).length = q.bitWidth
  hashModulus : BinaryArithmetic.toNat (a.stacks 707) = q.clauses.length
  ringShape : (a.stacks 280).length = d * baseWidth 3 q.p.t
  low : ∀ i : Fin 56, a.stacks (lowStack (Factor.nativeStacks (Memory.lowPort i))) =
    low q.ctx i
  oneBytes : a.stacks 69 = Product.bytes one
  minusBytes : a.stacks 76 = RingProgram.flat q.minus
  tape : a.stacks 143 = IdempotentApplyProgram.triplesTape q.digits
  shape : (a.stacks 88).length = n
  clauseOutput : a.stacks 63 = []
  clauseWork : ∀ i ∈ FactorServices.clauseScratch,
    a.stacks (lowStack (Clause.callerStacks i)) = []

variable {r Q n d A S : ℕ} {q : Factor.Spec r Q n d}
  {one seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d}
  {a : FactorAssignmentProgram.Data} {f : ℕ}

theorem Input.fetched_stacks (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    (fetched q a f rf).stacks = Function.update a.stacks 154
      (LeafFactorDispatchProgram.selectedPayload q.rawRows q.clauses q.marked q.mark f) := by
  rw [fetched, dispatched_stacks a rf q.rawRows q.clauses q.marked q.mark f
    h.rows h.clauses h.count h.mark, callbackInitial_stacks a h.blank]

theorem Input.fetched_frame (h : Input q A S one seed a f) (rf : Fin 8 → Bool)
    (i : Fin 896) (hi : i ≠ 154) : (fetched q a f rf).stacks i = a.stacks i := by
  rw [h.fetched_stacks rf, Function.update_of_ne hi]

theorem Input.fetched_low_frame (h : Input q A S one seed a f) (rf : Fin 8 → Bool)
    (i : Fin 768) (hi : i ≠ 154) :
    (projectState id lowStack (fetched q a f rf)).stacks i = a.stacks (lowStack i) := by
  apply h.fetched_frame rf
  intro he
  exact hi (Fin.ext (congrArg (fun k : Fin 896 => k.val) he))

/-- A selected record is bounded by the actual serialized master containing
it. This includes the neutral empty payload. -/
theorem Input.payload_length (h : Input q A S one seed a f) :
    (LeafFactorDispatchProgram.selectedPayload q.rawRows q.clauses q.marked q.mark f).length ≤ A := by
  unfold LeafFactorDispatchProgram.selectedPayload
  split_ifs with hh hm
  · rw [List.getD_eq_getElem _ _ hh]
    exact (HashInputProgram.Loop.original_payload_length_le q.rawRows _
      (List.getElem_mem hh)).trans (by rw [← h.rows]; exact h.incoming 701)
  · have hb : q.marked = true := (Bool.and_eq_true_iff.mp hm).1
    have hv : q.mark < q.clauses.length := by
      simpa only [Factor.Spec.clauses, HashInputProgram.Expansion.encodedClauses,
        List.length_map] using q.markValid hb
    rw [List.getD_eq_getElem _ _ hv]
    exact (HashInputProgram.Loop.original_payload_length_le q.clauses _
      (List.getElem_mem hv)).trans (by rw [← h.clauses]; exact h.incoming 700)
  · simp

theorem Input.fetched_wordBound (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    ∀ i, ((fetched q a f rf).stacks i).length ≤ A := by
  intro i
  rw [h.fetched_stacks rf]
  by_cases hi : i = 154
  · subst i
    simpa only [Function.update_self] using h.payload_length
  · simpa only [Function.update_of_ne hi] using h.incoming i

/-- Source master words survive dispatch and the concrete unary factor-ID
conversion; only the selected payload154 and selected-factor word556 change. -/
theorem Input.table_frame (h : Input q A S one seed a f) (rf : Fin 8 → Bool)
    (i : Fin 768) (hi154 : FactorTableProgram.basePort i ≠ 154)
    (hi556 : FactorTableProgram.basePort i ≠ 556) :
    (projectState id FactorTableProgram.basePort
      (FactorAssignmentBranches.tableInput (fetched q a f rf) f)).stacks i =
      (projectState localRegister FactorTableProgram.basePort a).stacks i := by
  change (FactorAssignmentBranches.identified (fetched q a f rf) f).stacks
    (FactorTableProgram.basePort i) = a.stacks (FactorTableProgram.basePort i)
  rw [FactorAssignmentBranches.identified_stacks, Function.update_of_ne hi556,
    h.fetched_frame rf _ hi154]

theorem Input.table_scalar (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    FactorTableNative.ScalarMasters q.p.t q.p.model q.p.modulus q.p.cache q.J q.p.R
      q.theta (projectState id FactorTableProgram.basePort
        (FactorAssignmentBranches.tableInput (fetched q a f rf) f)) n := by
  have H := h.table_frame rf
  refine ⟨h.scalar.widthPositive, h.scalar.zeroCanonical, h.scalar.zeroBits,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [H 194 (by decide) (by decide)]; exact h.scalar.modulus
  · rw [H 202 (by decide) (by decide)]; exact h.scalar.width
  · rw [H 203 (by decide) (by decide)]; exact h.scalar.zero
  · rw [H 201 (by decide) (by decide)]; exact h.scalar.table
  · rw [H 204 (by decide) (by decide)]; exact h.scalar.degree
  · rw [H 145 (by decide) (by decide)]; exact h.scalar.choicesLength
  · rw [H 280 (by decide) (by decide)]; exact h.scalar.zeroWord
  · rw [H 207 (by decide) (by decide)]; exact h.scalar.oneWord
  · rw [H 78 (by decide) (by decide)]; exact h.scalar.thetaWord
  · rw [H 128 (by decide) (by decide)]; exact h.scalar.ambientCount
  · rw [H 243 (by decide) (by decide)]; exact h.scalar.targetCount
  · rw [H 138 (by decide) (by decide)]; exact h.scalar.radius
  · rw [H 703 (by decide) (by decide)]; exact h.scalar.highLength

theorem Input.table_masters (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    FactorTableNative.SourceMasters q.p q.ps q.packing
      (projectState id FactorTableProgram.basePort
        (FactorAssignmentBranches.tableInput (fetched q a f rf) f)) := by
  have H := h.table_frame rf
  constructor
  · rw [H 130 (by decide) (by decide)]; exact h.masters.colors
  · rw [H 131 (by decide) (by decide)]; exact h.masters.nodes
  · rw [H 132 (by decide) (by decide)]; exact h.masters.typeWidth
  · rw [H 710 (by decide) (by decide)]; exact h.masters.positive
  · rw [H 711 (by decide) (by decide)]; exact h.masters.negative
  · rw [H 140 (by decide) (by decide)]; exact h.masters.scalarWidth
  · rw [H 712 (by decide) (by decide)]; exact h.masters.power
  · exact h.masters.powerNegative
  · rw [H 138 (by decide) (by decide)]; exact h.masters.radius
  · rw [H 139 (by decide) (by decide)]; exact h.masters.offset
  · rw [H 135 (by decide) (by decide)]; exact h.masters.metadata
  · rw [H 136 (by decide) (by decide)]; exact h.masters.plans
  · rw [H 713 (by decide) (by decide)]; exact h.masters.inverses
  · rw [H 714 (by decide) (by decide)]; exact h.masters.negatives
  · rw [H 715 (by decide) (by decide)]; exact h.masters.differences
  · rw [H 717 (by decide) (by decide)]; exact h.masters.ringWidth
  · rw [H 716 (by decide) (by decide)]; exact h.masters.rowWidth
  · rw [H 280 (by decide) (by decide)]; exact h.masters.zero
  · rw [H 207 (by decide) (by decide)]; exact h.masters.one
  · rw [H 211 (by decide) (by decide)]; exact h.masters.minusOne
  · rw [H 728 (by decide) (by decide)]; exact h.masters.inverseDenominator

/-- The actual source-table readiness is derived from fixed physical masters
and the already stored original ID; it is not provided by a caller service. -/
theorem Input.table_ready (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    FactorTableNative.Ready q.p q.ps q.packing q.u q.J n f A S q.theta
      (FactorAssignmentBranches.tableInput (fetched q a f rf) f) := by
  apply FactorTableNative.Ready.of_masters q.hu q.hJ (h.table_scalar rf) (h.table_masters rf)
  · change (FactorAssignmentBranches.identified (fetched q a f rf) f).stacks 556 = _
    simp only [FactorAssignmentBranches.identified_stacks, Function.update_self]
  · change ((FactorAssignmentBranches.identified (fetched q a f rf) f).stacks 857).length = n
    rw [FactorAssignmentBranches.identified_stacks, Function.update_of_ne (by decide),
      h.fetched_frame rf 857 (by decide)]
    exact h.correction
  · intro i
    change ((FactorAssignmentBranches.identified (fetched q a f rf) f).stacks i).length ≤ A
    rw [FactorAssignmentBranches.identified_stacks]
    by_cases hi : i = 556
    · subst i
      have hf := h.incoming 149
      rw [h.factor, List.length_reverse] at hf
      simp only [Encoding.length_encodeNat] at hf
      simp only [Function.update_self, List.length_replicate]
      omega
    · rw [Function.update_of_ne hi]
      exact h.fetched_wordBound rf i
  · exact h.size
  · exact h.radius

/-- The hash source bytes are the actual row selected by f, in the unchanged
original raw-row order. No arbitrary raw payload is assumed. -/
theorem Input.fetched_hash (h : Input q A S one seed a f) (rf : Fin 8 → Bool)
    (hf : f < q.rows.length) :
    Factor.HashInput q.ctx q.minus one seed q.source q.rows[f] q.digits q.bitWidth
      (projectState id lowStack (fetched q a f rf)) := by
  have H := h.fetched_low_frame rf
  constructor
  · change (fetched q a f rf).stacks 154 = _
    rw [h.fetched_stacks rf]
    simp [LeafFactorDispatchProgram.selectedPayload, Factor.Spec.rawRows, hf]
  · exact (H 700 (by decide)).trans
      (h.clauses.trans (HashInputProgram.Expansion.original_source_bytes q.source))
  · rw [H 708 (by decide)]; exact h.hashWidth
  · rw [H 707 (by decide)]; exact h.hashModulus
  · rw [H 280 (by decide)]; exact h.ringShape
  · exact (H 64 (by decide)).trans (h.blank 64 (by decide))
  · intro i hi
    have hn : i ≠ 154 := by
      intro he
      subst i
      norm_num [Expansion.scratch, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hi
    rw [H i hn]
    apply h.blank i
    simp only [callbackScratch, List.mem_append]
    exact Or.inl (Or.inr hi)
  · exact (H 358 (by decide)).trans (h.blank 358 (by decide))
  · exact (H 359 (by decide)).trans (h.blank 359 (by decide))
  · intro i
    rw [Factor.indicatorStacks_low, H _ (Factor.low_ne i 154 (by decide))]
    exact h.low i
  · exact (H 69 (by decide)).trans h.oneBytes
  · exact (H 76 (by decide)).trans h.minusBytes
  · exact (H 143 (by decide)).trans h.tape
  · rw [H 88 (by decide)]; exact h.shape
  · intro i hi
    have hn : Factor.indicatorStacks i ≠ 154 :=
      (by decide : ∀ i ∈ FactorServices.indicatorScratch,
        Factor.indicatorStacks i ≠ (154 : Fin 768)) i hi
    rw [H _ hn]
    apply h.blank
    simp only [callbackScratch, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨i, hi, rfl⟩))))
  · exact (H 151 (by decide)).trans h.seedBytes
  · exact (H 159 (by decide)).trans (h.blank 159 (by decide))

/-- Actual marked-clause bytes retain literal polarity and original variable
IDs; this is the source's clause-violation expression, not its complement. -/
theorem Input.fetched_marked (h : Input q A S one seed a f) (rf : Fin 8 → Bool)
    (hm : q.marked = true) (hf : f = q.rows.length) :
    let state := projectState id lowStack (fetched q a f rf)
    state.stacks 154 = Encoding.encodeList id (q.markedClause.map Clause.literalBits) ∧
      state.stacks 63 = [] ∧
      (∀ i, state.stacks (Clause.callerStacks (Memory.lowPort i)) = IdempotentApplyProgram.Steps.low q.ctx i) ∧
      state.stacks 69 = Product.bytes one ∧ state.stacks 76 = RingProgram.flat q.minus ∧
      (∀ i ∈ FactorServices.clauseScratch, state.stacks (Clause.callerStacks i) = []) ∧
      state.stacks 151 = Product.bytes seed ∧ state.stacks 159 = [] := by
  dsimp only
  have H := h.fetched_low_frame rf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have he : f = q.rawRows.length := by simpa [Factor.Spec.rawRows] using hf
    have hv := q.markValid hm
    have hp : q.markedClause = q.source[q.mark] := by
      simp [Factor.Spec.markedClause, List.getElem?_eq_getElem hv]
    change (fetched q a f rf).stacks 154 = _
    rw [h.fetched_stacks rf]
    have payload (ls : List (SAT.Literal (Fin n))) :
        HashInputProgram.clausePayload ls = Encoding.encodeList id (ls.map Clause.literalBits) := by
      induction ls with
      | nil => rfl
      | cons l ls ih =>
          change true :: (Encoding.frame (Encoding.encodeNat (Encoding.literalCode l)) ++
            HashInputProgram.clausePayload ls) = _
          simp only [List.map_cons, Encoding.encodeList, Clause.literalBits, ih, id_eq]
    simp [LeafFactorDispatchProgram.selectedPayload, he, hm, Factor.Spec.clauses,
      HashInputProgram.Expansion.encodedClauses, hp, List.getElem?_eq_getElem hv, payload]
  · exact (H 63 (by decide)).trans h.clauseOutput
  · intro i
    change (projectState id lowStack (fetched q a f rf)).stacks
      (Factor.nativeStacks (Memory.lowPort i)) = _
    rw [H _ (Factor.low_ne i 154 (by decide))]
    exact h.low i
  · exact (H 69 (by decide)).trans h.oneBytes
  · exact (H 76 (by decide)).trans h.minusBytes
  · intro i hi
    have hn : Clause.callerStacks i ≠ 154 :=
      (by decide : ∀ i ∈ FactorServices.clauseScratch,
        Clause.callerStacks i ≠ (154 : Fin 768)) i hi
    rw [H _ hn]
    exact h.clauseWork i hi
  · exact (H 151 (by decide)).trans h.seedBytes
  · exact (H 159 (by decide)).trans (h.blank 159 (by decide))

/-- The table-private boundary is unaffected by the selected payload port. -/
theorem Input.table_private (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 →
      (fetched q a f rf).stacks i = [] := by
  intro i hi h62 h556
  have hn : i ≠ 154 := by
    intro he
    subst i
    exact FactorTableSpace.caller_port_not_written 154 (Or.inl (by decide)) hi
  rw [h.fetched_frame rf i hn]
  exact h.tableBlank i hi h62 h556

/-- The source-table projection uses the current ambient assignment and fixed
high data, exactly as the original source factor does. -/
theorem Input.staged_factorJet (h : Input q A S one seed a f)
    (rf : Fin 8 → Bool) (j : ℕ) :
    PerturbationAssembly.sourceIncidenceJet q.p q.ps q.packing n f j q.theta
      (FactorTableProgram.projectBase
        (FactorTableProgram.staged
          (FactorAssignmentBranches.tableInput (fetched q a f rf) f)).stacks) =
      Factor.factorJet q.p q.ps q.packing n f j q.theta (a.stacks ∘ lowStack) := by
  let input := FactorAssignmentBranches.tableInput (fetched q a f rf) f
  let old := projectState id FactorTableProgram.basePort (FactorTableProgram.initialized input)
  have hp := congrArg StructuredProgram.State.stacks (FactorTableNative.project_staged input)
  change FactorTableProgram.projectBase (FactorTableProgram.staged input).stacks =
    (Incidence.staged old).stacks at hp
  rw [hp]
  have he := Factor.factorJet_staged q.p q.ps q.packing q.J n f j q.theta old
    ((h.table_scalar rf).initialized input)
  apply he.trans
  refine Factor.factorJet_frame q.p q.ps q.packing n f j q.theta old.stacks
    (a.stacks ∘ lowStack) ?_ ?_ ?_
  all_goals dsimp only [old, projectState, Function.comp_apply]
  · exact (FactorTableSpace.initialized_base_external input 145 (by decide)).trans
      (h.table_frame rf 145 (by decide) (by decide))
  · exact (FactorTableSpace.initialized_base_external input 702 (by decide)).trans
      (h.table_frame rf 702 (by decide) (by decide))
  · exact (FactorTableSpace.initialized_base_external input 703 (by decide)).trans
      (h.table_frame rf 703 (by decide) (by decide))

/-- Correction specialization retains the precise current U word, separately
from the high mask and current-head mask. -/
theorem Input.staged_correction (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    (FactorTableProgram.staged
      (FactorAssignmentBranches.tableInput (fetched q a f rf) f)).stacks 857 = a.stacks 857 := by
  rw [FactorTableNative.staged_mask]
  change (FactorAssignmentBranches.identified (fetched q a f rf) f).stacks 857 = _
  rw [FactorAssignmentBranches.identified_stacks, Function.update_of_ne (by decide)]
  exact h.fetched_frame rf 857 (by decide)

/-- The exact entries consumed by native arithmetic have the original source
meaning. The byte-injectivity theorem transports denotation without replacing
those entries by another valid representation. -/
theorem Input.payload_correct (h : Input q A S one seed a f)
    (rf : Fin 8 → Bool) (v : Fin n)
    (entries : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (hm : FactorTableNative.PayloadMeaning q.p q.ps q.packing q.u q.J n f q.theta
      (FactorTableProgram.staged
        (FactorAssignmentBranches.tableInput (fetched q a f rf) f)).stacks v.val
      (Product.bytes entries)) :
    TruncatedRingProgram.Good ∅ q.u q.J entries ∧
      TruncatedRingProgram.rawDenote q.p.ops.decode entries =
        FactorTableDenotation.specializedJet q.u q.J (a.stacks 857)
          (Factor.factorJet q.p q.ps q.packing n f v.val q.theta (a.stacks ∘ lowStack)) := by
  have hc := (h.table_ready rf).staged_common
  have hv := FactorTableDenotation.payload_typed_correct q.p q.ps q.packing
    q.u q.J n f v.val q.hu q.hJ q.theta _ _ hc.choicesLength hc.zeroWord hc.oneWord hm entries rfl
  rw [h.staged_correction rf, h.staged_factorJet rf v.val] at hv
  exact hv

/-- The explicit paid ordinary-branch cost, on the exact dispatched state. -/
def hashBranchBudget (q : Factor.Spec r Q n d) (A S width : ℕ)
    (a : FactorAssignmentProgram.Data) (f : ℕ) (hf : f < q.rows.length) (rf : Fin 8 → Bool) : ℕ :=
  7 * (f + 1) + 7 +
    FactorAssignmentBranches.tableTime q.p q.u q.J n A S (fetched q a f rf) f +
    (9 * ((fetched q a f rf).stacks 154).length + 11 +
      HashInputProgram.Loop.uniformBudget q.p.t (d-1) q.bitWidth
        ((fetched q a f rf).stacks 707) q.clauses q.rows[f].length +
      FactorEvaluationSpace.serviceBudget (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length)

/-- Actual ordinary dispatch, table production, expansion, indicator,
accumulator multiplication and record return, specialized to q.ctx. -/
theorem hash_callback_eval (h : Input q A S one seed a f)
    (hone : NativeSemantics.Good ∅ q.u q.J one)
    (hseed : NativeSemantics.Good ∅ q.u q.J seed)
    (hf : f < q.rows.length) (width : ℕ)
    (hwidth : ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
      w.literals.length ≤ width) :
    ∃ (rf : Fin 8 → Bool)
      (incidence : Fin n → FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
      (steps : ℕ) (z : FactorAssignmentProgram.Data),
      (∀ v, TruncatedRingProgram.Good ∅ q.u q.J (incidence v)) ∧
      (∀ v, TruncatedRingProgram.rawDenote q.p.ops.decode (incidence v) =
        FactorTableDenotation.specializedJet q.u q.J (a.stacks 857)
          (Factor.factorJet q.p q.ps q.packing n f v.val q.theta (a.stacks ∘ lowStack))) ∧
      let result := Product.run 3 q.p.t q.ctx.modulus q.ctx.cache q.ctx.table q.u q.J seed
        (Indicator.result q.ctx q.minus one incidence
          (HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f]) q.digits) []
      NativeSemantics.Good ∅ q.u q.J result ∧
      steps ≤ clearCallbackCost a + 9 * (a.stacks 149).length + 14 +
        LeafFactorDispatchProgram.budget q.rawRows q.clauses q.mark f +
        hashBranchBudget q A S width a f hf rf ∧
      Eval FactorAssignmentProgram.callback steps a z ∧
      z.stacks = Function.update (Function.update a.stacks 149 []) 151 (Product.bytes result) ∧
      z.regs 13 = false ∧ z.regs 14 = true ∧ z.regs 15 = false := by
  have hvalid : q.marked = true → q.mark < q.clauses.length := by
    simpa only [Factor.Spec.clauses, HashInputProgram.Expansion.encodedClauses, List.length_map]
      using q.markValid
  obtain ⟨kd,rf,hkd,hd,h5,_⟩ := dispatch_eval a q.rawRows q.clauses q.marked q.mark f
    h.rows h.clauses h.count h.mark h.flag h.factor hvalid
  have hn : f < q.rawRows.length := by simpa only [Factor.Spec.rawRows, List.length_map] using hf
  have hrole : (fetched q a f rf).regs 5 = true := by simpa [fetched, hn] using h5
  have hid : (fetched q a f rf).stacks 149 = (Encoding.encodeNat f).reverse :=
    (h.fetched_frame rf 149 (by decide)).trans h.factor
  have h556 : (fetched q a f rf).stacks 556 = [] :=
    (h.fetched_frame rf 556 (by decide)).trans (h.blank 556 (by decide))
  have h62 : (fetched q a f rf).stacks 62 = [] :=
    (h.fetched_frame rf 62 (by decide)).trans (h.blank 62 (by decide))
  obtain ⟨incidence,kb,b,hgood,hmeaning,hkb,hresult,heb,hstore⟩ :=
    FactorAssignmentBranches.hashFactor_eval q.p q.ps q.packing q.ctx f A S q.theta q.minus
      one seed hone hseed q.source q.rows[f] q.digits q.bitWidth width q.bitWidthPositive
      q.sourceBound hwidth (fetched q a f rf) hid h556 h62 (h.table_ready rf)
      (h.table_private rf) (h.fetched_hash rf hf)
  have he := callback_chosen_eval a b rf q.rawRows q.clauses q.marked q.mark f kd (kb+1) _
    h.rows h.clauses h.count h.mark h.blank hd (choose_hash hrole heb) hstore
  refine ⟨rf,incidence,_,callbackFinished b,hgood,?_,hresult,?_,he.1,
    he.2.1,he.2.2.1,he.2.2.2.1,he.2.2.2.2⟩
  · intro v
    exact (h.payload_correct rf v (incidence v) (hmeaning v)).2
  · change kb ≤ hashBranchBudget q A S width a f hf rf at hkb
    omega

/-- Explicit paid cost of the actual marked-clause branch. -/
def markedBranchBudget (q : Factor.Spec r Q n d) (A S : ℕ)
    (a : FactorAssignmentProgram.Data) (f : ℕ) (rf : Fin 8 → Bool) : ℕ :=
  7 * (f + 1) + 7 +
    FactorAssignmentBranches.tableTime q.p q.u q.J n A S (fetched q a f rf) f +
    (9 * ((fetched q a f rf).stacks 154).length + 9 +
      FactorEvaluationSpace.serviceBudget (baseWidth 3 q.p.t) d n q.u q.J
        q.markedClause.length 0 0)

/-- Actual marked dispatch and clause violation arithmetic, retaining the
very specialized incidence entries returned by the table run. -/
theorem marked_callback_eval (h : Input q A S one seed a f)
    (hone : NativeSemantics.Good ∅ q.u q.J one)
    (hseed : NativeSemantics.Good ∅ q.u q.J seed)
    (hm : q.marked = true) (hf : f = q.rows.length) :
    ∃ (rf : Fin 8 → Bool)
      (incidence : Fin n → FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
      (steps : ℕ) (z : FactorAssignmentProgram.Data),
      (∀ v, TruncatedRingProgram.Good ∅ q.u q.J (incidence v)) ∧
      (∀ v, TruncatedRingProgram.rawDenote q.p.ops.decode (incidence v) =
        FactorTableDenotation.specializedJet q.u q.J (a.stacks 857)
          (Factor.factorJet q.p q.ps q.packing n f v.val q.theta (a.stacks ∘ lowStack))) ∧
      let result := Product.run 3 q.p.t q.ctx.modulus q.ctx.cache q.ctx.table q.u q.J seed
        (FactorServices.clauseResult q.ctx q.minus one incidence q.markedClause) []
      NativeSemantics.Good ∅ q.u q.J result ∧
      steps ≤ clearCallbackCost a + 9 * (a.stacks 149).length + 15 +
        LeafFactorDispatchProgram.budget q.rawRows q.clauses q.mark f +
        markedBranchBudget q A S a f rf ∧
      Eval FactorAssignmentProgram.callback steps a z ∧
      z.stacks = Function.update (Function.update a.stacks 149 []) 151 (Product.bytes result) ∧
      z.regs 13 = false ∧ z.regs 14 = true ∧ z.regs 15 = false := by
  have hvalid : q.marked = true → q.mark < q.clauses.length := by
    simpa only [Factor.Spec.clauses, HashInputProgram.Expansion.encodedClauses, List.length_map]
      using q.markValid
  obtain ⟨kd,rf,hkd,hd,h5,h6⟩ := dispatch_eval a q.rawRows q.clauses q.marked q.mark f
    h.rows h.clauses h.count h.mark h.flag h.factor hvalid
  have hn : f = q.rawRows.length := by simpa only [Factor.Spec.rawRows, List.length_map] using hf
  have hrole5 : (fetched q a f rf).regs 5 = false := by simpa [fetched, hn] using h5
  have hrole6 : (fetched q a f rf).regs 6 = true := by simpa [fetched, hm, hn] using h6
  have hid : (fetched q a f rf).stacks 149 = (Encoding.encodeNat f).reverse :=
    (h.fetched_frame rf 149 (by decide)).trans h.factor
  have h556 : (fetched q a f rf).stacks 556 = [] :=
    (h.fetched_frame rf 556 (by decide)).trans (h.blank 556 (by decide))
  have h359 : (fetched q a f rf).stacks 359 = [] :=
    (h.fetched_frame rf 359 (by decide)).trans (h.blank 359 (by decide))
  have h62 : (fetched q a f rf).stacks 62 = [] :=
    (h.fetched_frame rf 62 (by decide)).trans (h.blank 62 (by decide))
  obtain ⟨hraw, houtput, hlow, honeBytes, hminus, hwork, hseedBytes, htemporary⟩ :=
    h.fetched_marked rf hm hf
  obtain ⟨incidence,kb,b,hgood,hmeaning,hkb,hresult,heb,hstore⟩ :=
    FactorAssignmentBranches.markedFactor_eval q.p q.ps q.packing q.ctx f A S q.theta q.minus
      one seed hone hseed q.markedClause (fetched q a f rf) hid h556 h359 h62
      (h.table_ready rf) (h.table_private rf) hraw houtput hlow honeBytes hminus
      hwork hseedBytes htemporary
  have he := callback_chosen_eval a b rf q.rawRows q.clauses q.marked q.mark f kd (kb+2) _
    h.rows h.clauses h.count h.mark h.blank hd (choose_marked hrole5 hrole6 heb) hstore
  refine ⟨rf,incidence,_,callbackFinished b,hgood,?_,hresult,?_,he.1,
    he.2.1,he.2.2.1,he.2.2.2.1,he.2.2.2.2⟩
  · intro v
    exact (h.payload_correct rf v (incidence v) (hmeaning v)).2
  · change kb ≤ markedBranchBudget q A S a f rf at hkb
    omega

/-- Neutral original IDs execute their paid record path and preserve the
complete accumulated dictionary. -/
theorem neutral_callback_eval (h : Input q A S one seed a f)
    (hseed : NativeSemantics.Good ∅ q.u q.J seed)
    (hh : ¬ f < q.rows.length)
    (hm : (q.marked && decide (f = q.rows.length)) = false) :
    ∃ steps z,
      NativeSemantics.Good ∅ q.u q.J seed ∧
      steps ≤ clearCallbackCost a + 9 * (a.stacks 149).length + 15 +
        LeafFactorDispatchProgram.budget q.rawRows q.clauses q.mark f ∧
      Eval FactorAssignmentProgram.callback steps a z ∧
      z.stacks = Function.update (Function.update a.stacks 149 []) 151 (Product.bytes seed) ∧
      z.regs 13 = false ∧ z.regs 14 = true ∧ z.regs 15 = false := by
  have hvalid : q.marked = true → q.mark < q.clauses.length := by
    simpa only [Factor.Spec.clauses, HashInputProgram.Expansion.encodedClauses, List.length_map]
      using q.markValid
  obtain ⟨steps,z,hs,he,hz,h13,h14,h15⟩ := callback_neutral_frame a q.rawRows q.clauses
    q.marked q.mark f h.rows h.clauses h.count h.mark h.flag h.factor hvalid
    (by simpa only [Factor.Spec.rawRows, List.length_map] using hh)
    (by simpa only [Factor.Spec.rawRows, List.length_map] using hm) h.blank
  refine ⟨steps,z,hseed,hs,he,?_,h13,h14,h15⟩
  rw [hz]
  symm
  apply Function.update_eq_self_iff.mpr
  simpa only [Function.update_of_ne (show (151 : Fin 896) ≠ 149 by decide)] using h.seedBytes.symm

/-- Dense multiplication for the same selected native factor. The source jet
uses all original factor IDs, but the concrete incidence family is the one
just produced for f; no table for other IDs is constructed or assumed. -/
theorem selected_step_value
    (s : Fin 768 → List Bool) (mask : List Bool)
    (incidence : Fin n → FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (hone : NativeSemantics.Good ∅ q.u q.J one)
    (hseed : NativeSemantics.Good ∅ q.u q.J seed)
    (honeval : NativeSemantics.rawDenote q.p.ops.decode one =
      Squarefree.canonical q.u q.J 1)
    (hi : ∀ v, TruncatedRingProgram.Good ∅ q.u q.J (incidence v))
    (hinc : ∀ v, TruncatedRingProgram.rawDenote q.p.ops.decode (incidence v) =
      FactorTableDenotation.specializedJet q.u q.J mask
        (Factor.factorJet q.p q.ps q.packing n f v.val q.theta s))
    (factor : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (hfactor : AssignmentSemantics.selectedFactor q.ctx q.minus one (fun _ => incidence)
      (AssignmentConcrete.weightedHashes q) q.marked q.markedClause q.digits f = some factor) :
    let result := Product.run 3 q.p.t q.ctx.modulus q.ctx.cache q.ctx.table q.u q.J seed factor []
    NativeSemantics.Good ∅ q.u q.J result ∧
      TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode result =
        TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode seed *
          QueryEvaluation.specializeDense q.u q.J
            (fun v => decide (v ∈ Squarefree.decodeMask n mask)) (q.value s f) := by
  have scalarize {R : Type} [CommRing R] {m : ℕ} (u J : ℕ) (mask : List Bool)
      (jet : Squarefree.Jet (Fin m) R) :
      FactorTableDenotation.specializedJet u J mask jet =
        Squarefree.canonical u J (Moments.jetScalar (Moments.jetEval
          (Squarefree.boolValue (fun v => decide (v ∈ Squarefree.decodeMask m mask)))
          (Squarefree.boolValue_idempotent _) jet)) := by
    have hvalue : (fun v : Fin m => if v ∈ Squarefree.decodeMask m mask then (1 : R) else 0) =
        Squarefree.boolValue (fun v => decide (v ∈ Squarefree.decodeMask m mask)) := by
      funext v
      simp [Squarefree.boolValue]
    simp only [FactorTableDenotation.specializedJet, hvalue]
  have rawEq {R : Type} [CommRing R] {m B e : ℕ}
      (decode : RingProgram.Code (Word B) e → R) (entries : List (Product.Entry m B e)) :
      NativeSemantics.rawDenote decode entries = TruncatedRingProgram.rawDenote decode entries := rfl
  let U : Fin n → Bool := fun v => decide (v ∈ Squarefree.decodeMask n mask)
  have hjet (v : Fin n) : NativeSemantics.rawDenote q.p.ops.decode (incidence v) =
      Squarefree.canonical q.u q.J
        (Moments.jetScalar (Moments.jetEval (Squarefree.boolValue U)
          (Squarefree.boolValue_idempotent U)
          (AssignmentConcrete.sourceJets q s f v))) := by
    unfold AssignmentConcrete.sourceJets
    exact (rawEq (R := q.p.model.O q.p.t) q.p.ops.decode (incidence v)).trans ((hinc v).trans
      (scalarize (R := q.p.model.O q.p.t) (m := n) q.u q.J mask
        (Factor.factorJet q.p q.ps q.packing n f v.val q.theta s)))
  have hh := QueryJetSemantics.selectedFactor_step_specialized_dense q.ctx
    (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t))
    (Factor.Semantics.context_table_correct q.p q.u q.J q.width q.widthLength)
    q.p.hd (Factor.Semantics.basis_zero q.p) q.hu q.hJ q.minus one seed
    (fun _ => incidence) hone hseed (fun _ v => ⟨(hi v).valid, (hi v).nodup⟩)
    q.minusValue honeval U (AssignmentConcrete.sourceJets q s)
    (AssignmentConcrete.weightedHashes q) q.marked q.markedClause f
    (fun _ _ _ l _ => hjet l.variable) (fun _ _ l _ => hjet l.variable)
    q.code factor hfactor
  refine ⟨hh.1, hh.2.trans ?_⟩
  exact congrArg (fun value => TruncatedRingProgram.rawValue q.u q.J
    q.p.ops.decode seed * QueryEvaluation.specializeDense q.u q.J U value)
    (AssignmentConcrete.value_eq_selectedValue q s f).symm

/-- The ordinary branch computes the precise original hash selected by f,
followed by multiplication into the same current seed. -/
theorem hash_step_value
    (s : Fin 768 → List Bool) (mask : List Bool)
    (incidence : Fin n → FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (hone : NativeSemantics.Good ∅ q.u q.J one)
    (hseed : NativeSemantics.Good ∅ q.u q.J seed)
    (honeval : NativeSemantics.rawDenote q.p.ops.decode one =
      Squarefree.canonical q.u q.J 1)
    (hi : ∀ v, TruncatedRingProgram.Good ∅ q.u q.J (incidence v))
    (hinc : ∀ v, TruncatedRingProgram.rawDenote q.p.ops.decode (incidence v) =
      FactorTableDenotation.specializedJet q.u q.J mask
        (Factor.factorJet q.p q.ps q.packing n f v.val q.theta s))
    (hf : f < q.rows.length) :
    let factor := Indicator.result q.ctx q.minus one incidence
      (HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f]) q.digits
    TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode
      (Product.run 3 q.p.t q.ctx.modulus q.ctx.cache q.ctx.table q.u q.J seed factor []) =
      TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode seed *
        QueryEvaluation.specializeDense q.u q.J
          (fun v => decide (v ∈ Squarefree.decodeMask n mask)) (q.value s f) := by
  apply (selected_step_value s mask incidence hone hseed honeval hi hinc _ ?_).2
  simp [AssignmentSemantics.selectedFactor, AssignmentConcrete.weightedHashes, hf]

/-- The marked branch retains the source clause's violation polynomial and
multiplies it into the same current seed. -/
theorem marked_step_value
    (s : Fin 768 → List Bool) (mask : List Bool)
    (incidence : Fin n → FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (hone : NativeSemantics.Good ∅ q.u q.J one)
    (hseed : NativeSemantics.Good ∅ q.u q.J seed)
    (honeval : NativeSemantics.rawDenote q.p.ops.decode one =
      Squarefree.canonical q.u q.J 1)
    (hi : ∀ v, TruncatedRingProgram.Good ∅ q.u q.J (incidence v))
    (hinc : ∀ v, TruncatedRingProgram.rawDenote q.p.ops.decode (incidence v) =
      FactorTableDenotation.specializedJet q.u q.J mask
        (Factor.factorJet q.p q.ps q.packing n f v.val q.theta s))
    (hm : q.marked = true) (hf : f = q.rows.length) :
    let factor := FactorServices.clauseResult q.ctx q.minus one incidence q.markedClause
    TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode
      (Product.run 3 q.p.t q.ctx.modulus q.ctx.cache q.ctx.table q.u q.J seed factor []) =
      TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode seed *
        QueryEvaluation.specializeDense q.u q.J
          (fun v => decide (v ∈ Squarefree.decodeMask n mask)) (q.value s f) := by
  apply (selected_step_value s mask incidence hone hseed honeval hi hinc _ ?_).2
  simp [AssignmentSemantics.selectedFactor, AssignmentConcrete.weightedHashes, hf, hm,
    FactorServices.clauseResult]

/-- The explicit cost keeps every dispatcher scan and every native branch.
It is a proof-side numerical envelope, never a traversal over possible states. -/
def callbackBudget (q : Factor.Spec r Q n d) (A S width : ℕ)
    (a : FactorAssignmentProgram.Data) (f : ℕ) (rf : Fin 8 → Bool) : ℕ :=
  clearCallbackCost a + 9 * (a.stacks 149).length + 15 +
    LeafFactorDispatchProgram.budget q.rawRows q.clauses q.mark f +
    if hf : f < q.rows.length then hashBranchBudget q A S width a f hf rf
    else if q.marked && decide (f = q.rows.length) then markedBranchBudget q A S a f rf else 0

/-- The concrete callback produces the exact specialized original factor
value. Its whole raw output, physical frame, paid execution, and arithmetic
meaning refer to one and the same actual execution. -/
theorem callback_eval_correct (h : Input q A S one seed a f)
    (hone : NativeSemantics.Good ∅ q.u q.J one)
    (hseed : NativeSemantics.Good ∅ q.u q.J seed)
    (honeval : NativeSemantics.rawDenote q.p.ops.decode one =
      Squarefree.canonical q.u q.J 1)
    (width : ℕ)
    (hwidth : ∀ hf : f < q.rows.length,
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length ≤ width) :
    ∃ (out : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
      (rf : Fin 8 → Bool) (steps : ℕ) (z : FactorAssignmentProgram.Data),
      NativeSemantics.Good ∅ q.u q.J out ∧
      TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode out =
        TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode seed *
          QueryEvaluation.specializeDense q.u q.J
            (fun v => decide (v ∈ Squarefree.decodeMask n (a.stacks 857)))
            (q.value (a.stacks ∘ lowStack) f) ∧
      steps ≤ callbackBudget q A S width a f rf ∧
      Eval FactorAssignmentProgram.callback steps a z ∧
      z.stacks = Function.update (Function.update a.stacks 149 []) 151 (Product.bytes out) ∧
      z.regs 13 = false ∧ z.regs 14 = true ∧ z.regs 15 = false := by
  by_cases hf : f < q.rows.length
  · obtain ⟨rf,incidence,k,z,hi,hinc,hout,hk,he,hz,h13,h14,h15⟩ :=
      hash_callback_eval h hone hseed hf width (hwidth hf)
    refine ⟨_,rf,k,z,hout,hash_step_value _ _ incidence hone hseed honeval hi hinc hf,
      ?_,he,hz,h13,h14,h15⟩
    simp only [callbackBudget, dite_eq_left hf]
    omega
  · by_cases hm : (q.marked && decide (f = q.rows.length)) = true
    · have hb : q.marked = true := (Bool.and_eq_true_iff.mp hm).1
      have hid : f = q.rows.length := of_decide_eq_true (Bool.and_eq_true_iff.mp hm).2
      obtain ⟨rf,incidence,k,z,hi,hinc,hout,hk,he,hz,h13,h14,h15⟩ :=
        marked_callback_eval h hone hseed hb hid
      refine ⟨_,rf,k,z,hout,marked_step_value _ _ incidence hone hseed honeval hi hinc hb hid,
        ?_,he,hz,h13,h14,h15⟩
      simpa only [callbackBudget, dite_eq_right hf, hm, ite_true] using hk
    · have hb : (q.marked && decide (f = q.rows.length)) = false :=
        Bool.eq_false_iff.mpr hm
      obtain ⟨k,z,hout,hk,he,hz,h13,h14,h15⟩ := neutral_callback_eval h hseed hf hb
      refine ⟨seed,(fun _ => false),k,z,hout,?_,?_,he,hz,h13,h14,h15⟩
      · simp only [Factor.Spec.value, dite_eq_right hf, hb, Bool.false_eq_true, ite_false,
          map_one, mul_one]
      · simpa only [callbackBudget, dite_eq_right hf, hb, Bool.false_eq_true, ite_false,
          Nat.add_zero] using hk

/-- Uniform source-table work: the actual staged high-mask word is bounded
by the entry's physical word cap, independently of dispatcher registers. -/
def tableBudget (q : Factor.Spec r Q n d) (A S : ℕ) : ℕ :=
  1000000 * (A + n +
    FactorTableNative.specializedLiteralWork q.p q.u q.J n S (1029*A+99) +
    FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d + 1)^2

theorem Input.tableTime_le (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    FactorAssignmentBranches.tableTime q.p q.u q.J n A S (fetched q a f rf) f ≤
      tableBudget q A S := by
  have hstage := FactorTableSpace.staged_stack_bound
    (FactorAssignmentBranches.tableInput (fetched q a f rf) f) A
    (h.table_ready rf).incoming 574
  have hwork : FactorTableNative.specializedLiteralWork q.p q.u q.J n S
      ((FactorTableProgram.staged
        (FactorAssignmentBranches.tableInput (fetched q a f rf) f)).stacks 574).length ≤
      FactorTableNative.specializedLiteralWork q.p q.u q.J n S (1029*A+99) := by
    unfold FactorTableNative.specializedLiteralWork
    omega
  apply (FactorTableSpace.commandBudget_le A n _ _).trans
  unfold tableBudget
  gcongr

theorem Input.factor_le (h : Input q A S one seed a f) : f ≤ A := by
  have hf := h.incoming 149
  rw [h.factor, List.length_reverse] at hf
  simp only [Encoding.length_encodeNat] at hf
  omega

/-- The actual dispatcher pays for all losing records in both encoded masters. -/
theorem Input.dispatchBudget_le (h : Input q A S one seed a f) :
    LeafFactorDispatchProgram.budget q.rawRows q.clauses q.mark f ≤ 102*A+138 := by
  have hrow := h.incoming 701
  have hclause := h.incoming 700
  have hcount := h.incoming 704
  have hmark := h.incoming 705
  rw [h.rows] at hrow
  rw [h.clauses] at hclause
  rw [h.count, List.length_replicate] at hcount
  rw [h.mark] at hmark
  simp only [Encoding.length_encodeNat] at hmark
  have hid := h.factor_le
  unfold LeafFactorDispatchProgram.budget LeafFactorDispatchProgram.dispatchBound
    LeafFactorDispatchProgram.branchBound
  omega

/-- The complete per-record bound is fixed before the record scan. Z bounds
only explicit source dimensions, serialized inputs and retained arithmetic
capacity; no evaluator or run is assumed. -/
def uniformCallbackBudget (q : Factor.Spec r Q n d) (A S Z : ℕ) : ℕ :=
  callbackScratch.length * (2*A+3) + 128*A+200 + tableBudget q A S +
    2000*Z^3 + 14000000*Z^9

theorem callbackBudget_le (h : Input q A S one seed a f) (width Z : ℕ)
    (hZ : 1 ≤ Z) (hA : A ≤ Z) (hbit : q.bitWidth ≤ Z)
    (hshape : d*baseWidth 3 q.p.t ≤ Z)
    (hhashScale : ∀ hf : f < q.rows.length,
      FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length ≤ Z)
    (hmarkScale : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
      q.markedClause.length 0 0 ≤ Z)
    (rf : Fin 8 → Bool) :
    callbackBudget q A S width a f rf ≤ uniformCallbackBudget q A S Z := by
  have hclear' : clearCallbackCost a ≤ callbackScratch.length * (2*A+3)+1 := by
    unfold clearCallbackCost
    have hc := SubexpSetupStorage.clearManyCost_le callbackScratch
      (projectState localRegister lowStack a) A (fun i => h.incoming (lowStack i))
    omega
  have hraw := h.incoming 149
  have hdispatch := h.dispatchBudget_le
  have htable := h.tableTime_le rf
  have hid := h.factor_le
  have hp : ((fetched q a f rf).stacks 154).length ≤ A := h.fetched_wordBound rf 154
  have hmod : ((fetched q a f rf).stacks 707).length ≤ Z :=
    (h.fetched_wordBound rf 707).trans hA
  have hclauses : (Encoding.encodeList id q.clauses).length ≤ Z := by
    rw [← h.clauses]
    exact (h.incoming 700).trans hA
  have hcount : q.clauses.length ≤ Z :=
    (Nat.le_succ _).trans ((Encoding.length_encodeList_lower id q.clauses).trans hclauses)
  by_cases hf : f < q.rows.length
  · have hs := hhashScale hf
    have hterms : q.rows[f].length ≤ Z := by
      unfold FactorEvaluationSpace.inputScale at hs
      omega
    have hexp := FactorBounds.expansionBound_le q.bitWidth
      ((fetched q a f rf).stacks 707).length q.clauses.length
      (Encoding.encodeList id q.clauses).length ((d-1+1)*baseWidth 3 q.p.t)
      q.rows[f].length Z hZ hbit hmod hcount hclauses
      (by simpa only [Nat.sub_add_cancel q.p.hd] using hshape) hterms
    change HashInputProgram.Loop.uniformBudget q.p.t (d-1) q.bitWidth
      ((fetched q a f rf).stacks 707) q.clauses q.rows[f].length ≤ 2000*Z^3 at hexp
    have hservice : FactorEvaluationSpace.serviceBudget (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length ≤ 14000000*Z^9 := by
      unfold FactorEvaluationSpace.serviceBudget
      gcongr
    simp only [callbackBudget, dite_eq_left hf, hashBranchBudget, uniformCallbackBudget]
    omega
  · have hservice : FactorEvaluationSpace.serviceBudget (baseWidth 3 q.p.t) d n q.u q.J
        q.markedClause.length 0 0 ≤ 14000000*Z^9 := by
      unfold FactorEvaluationSpace.serviceBudget
      gcongr
    simp only [callbackBudget, dite_eq_right hf, uniformCallbackBudget]
    split
    · unfold markedBranchBudget
      omega
    · omega

/-- A fixed ninth power bounds the callback's composed numerical envelope.
The degree does not depend on the input or the number of scanned factors. -/
theorem callback_cost_polynomial (a A n K L Z : ℕ) :
    a*(2*A+3)+128*A+200+1000000*(A+n+K+L+1)^2+2000*Z^3+14000000*Z^9 ≤
      16000000*(a+A+n+K+L+Z+1)^9 := by
  let X := a+A+n+K+L+Z+1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have ha : a ≤ X := by dsimp [X]; omega
  have hA : A ≤ X := by dsimp [X]; omega
  have hZ : Z ≤ X := by dsimp [X]; omega
  have hsum : A+n+K+L+1 ≤ X := by dsimp [X]; omega
  have h1 : 1 ≤ X^9 := Nat.one_le_pow _ _ hX
  have hx : X ≤ X^9 := by simpa using Nat.pow_le_pow_right hX (show 1 ≤ 9 by decide)
  have h2 : X^2 ≤ X^9 := Nat.pow_le_pow_right hX (by decide)
  have h3 : X^3 ≤ X^9 := Nat.pow_le_pow_right hX (by decide)
  have hclear : a*(2*A+3) ≤ 5*X^2 := by
    have hh : a*(2*A+3) ≤ X*(2*X+3) := by gcongr
    nlinarith
  have htable : (A+n+K+L+1)^2 ≤ X^2 := by gcongr
  have hz3 : Z^3 ≤ X^3 := by gcongr
  have hz9 : Z^9 ≤ X^9 := by gcongr
  change _ ≤ 16000000*X^9
  omega

/-- The only large service terms are the already explicit source and
specialization budgets, inside a fixed power. -/
theorem uniformCallbackBudget_polynomial (q : Factor.Spec r Q n d) (A S Z : ℕ) :
    uniformCallbackBudget q A S Z ≤
      16000000 * (callbackScratch.length + A + n +
        FactorTableNative.specializedLiteralWork q.p q.u q.J n S (1029*A+99) +
        FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d + Z + 1)^9 := by
  exact callback_cost_polynomial callbackScratch.length A n _ _ Z

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback

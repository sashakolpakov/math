import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorReadyInput

namespace OAI.Algorithms

/-! Actual fetched payloads, not assumed row evaluators, provide the native
hash and marked-clause inputs from the fixed physical node invariant. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorReady
open SubexponentialSAT BitProgram StructuredCalls MomentsProgram SubexpSetupStorage
open PerturbationAssembly SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native IdempotentApplyProgram.Steps
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q n d : ℕ} {q : Factor.Spec r Q n d} {S A : ℕ} {base : Fin 768 → List Bool}

private theorem expansionScratch_disjoint : ∀ i ∈ Expansion.scratch,
    i ∉ ([149,150,151,154] : List (Fin 768)) := by
  intro i hi
  simp only [Expansion.scratch, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl <;> simp

private theorem nativeLow_disjoint : ∀ i : Fin 56,
    Factor.nativeStacks (Memory.lowPort i) ∉ ([149,150,151,154] : List (Fin 768)) := by
  intro i
  simp [Factor.nativeStacks, Memory.lowPort, Fin.ext_iff]
  omega

private theorem indicatorScratch_disjoint : ∀ i ∈ FactorServices.indicatorScratch,
    Factor.indicatorStacks i ∉ ([149,150,151,154] : List (Fin 768)) := by
  intro i hi
  simp only [FactorServices.indicatorScratch, List.mem_cons, List.mem_nil_iff,
    or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [Factor.indicatorStacks, Factor.nativeStacks, Fin.ext_iff,
      Equiv.swap_apply_def]

private theorem clauseLow_disjoint : ∀ i : Fin 56,
    Clause.callerStacks (Memory.lowPort i) ∉ ([149,150,151,154] : List (Fin 768)) := by
  intro i
  simp [Clause.callerStacks, Memory.lowPort, Fin.ext_iff]
  omega

private theorem clauseScratch_disjoint : ∀ i ∈ FactorServices.clauseScratch,
    Clause.callerStacks i ∉ ([149,150,151,154] : List (Fin 768)) := by
  intro i hi
  simp only [FactorServices.clauseScratch, List.mem_cons, List.mem_nil_iff,
    or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [Clause.callerStacks, Fin.ext_iff]

def fetched (q : Factor.Spec r Q n d) (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (seed : FactorLoop.Raw n (baseWidth 3 q.p.t) d) (tail : List Bool) (f : ℕ) : Factor.Data :=
  payloadState base regs seed tail f
    (LeafFactorDispatchProgram.selectedPayload q.rawRows q.clauses q.marked q.mark f)

theorem fetched_frame (regs : Fin 40 → Bool) (seed : FactorLoop.Raw n (baseWidth 3 q.p.t) d)
    (tail : List Bool) (f : ℕ) (i : Fin 768)
    (hi : i ∉ ([149,150,151,154] : List (Fin 768))) :
    (fetched q base regs seed tail f).stacks i=base i := by
  simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at hi
  simp [fetched,payloadState,FactorLoop.state,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2]

theorem fetched_seed (regs : Fin 40 → Bool) (seed : FactorLoop.Raw n (baseWidth 3 q.p.t) d)
    (tail : List Bool) (f : ℕ) :
    (fetched q base regs seed tail f).stacks 151=Product.bytes seed := by
  simp [fetched,payloadState,FactorLoop.state]

theorem Input.fetched_hash (h : Input q S A base) (regs : Fin 40 → Bool)
    (seed : FactorLoop.Raw n (baseWidth 3 q.p.t) d) (tail : List Bool) (f : ℕ)
    (hf : f < q.rows.length) :
    Factor.HashInput q.ctx q.minus q.one seed q.source q.rows[f] q.digits q.bitWidth
      (fetched q base regs seed tail f) := by
  have H := fetched_frame (q:=q) (base:=base) regs seed tail f
  constructor
  · have hfr : f < q.rawRows.length := by simpa [Factor.Spec.rawRows] using hf
    simp [fetched,payloadState,LeafFactorDispatchProgram.selectedPayload,
      Factor.Spec.rawRows,hf]
  · exact (H 700 (by decide)).trans (h.clauses.trans (HashInputProgram.Expansion.original_source_bytes q.source))
  · rw [H 708 (by decide)]; exact h.hashWidth
  · rw [H 707 (by decide)]; exact h.hashModulus
  · rw [H 280 (by decide)]
    exact (congrArg List.length h.caller.zeroWord).trans (RingProgram.flat_length _)
  · exact (H 64 (by decide)).trans (h.blank 64 (by simp))
  · intro i hi
    exact (H i (expansionScratch_disjoint i hi)).trans (h.expand i hi)
  · exact (H 358 (by decide)).trans h.work358
  · exact (H 359 (by decide)).trans h.work359
  · intro i
    rw [Factor.indicatorStacks_low]
    exact (H _ (nativeLow_disjoint i)).trans (h.low i)
  · exact (H 69 (by decide)).trans h.one
  · exact (H 76 (by decide)).trans h.minus
  · exact (H 143 (by decide)).trans h.tape
  · rw [H 88 (by decide)]; exact h.shape
  · intro i hi
    exact (H _ (indicatorScratch_disjoint i hi)).trans (h.indicatorWork i hi)
  · exact fetched_seed regs seed tail f
  · exact (H 159 (by decide)).trans (h.blank 159 (by simp))

theorem literal_payload (ls : List (SAT.Literal (Fin n))) :
    Encoding.encodeList (fun l => Encoding.encodeNat (Encoding.literalCode l)) ls=
      Encoding.encodeList id (ls.map Clause.literalBits) := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [Encoding.encodeList,Clause.literalBits,ih]

theorem Input.fetched_marked (h : Input q S A base) (regs : Fin 40 → Bool)
    (seed : FactorLoop.Raw n (baseWidth 3 q.p.t) d) (tail : List Bool) (f : ℕ)
    (hm : q.marked=true) (hf : f=q.rows.length) :
    Factor.MarkedInput q.ctx q.minus q.one seed q.markedClause
      (fetched q base regs seed tail f) := by
  have H := fetched_frame (q:=q) (base:=base) regs seed tail f
  constructor
  · have he : f=q.rawRows.length := by simpa [Factor.Spec.rawRows] using hf
    have hv := q.markValid hm
    simp [fetched,payloadState,LeafFactorDispatchProgram.selectedPayload,he,hm,
      Factor.Spec.clauses,HashInputProgram.Expansion.encodedClauses,
      Factor.Spec.markedClause,
      List.getElem?_eq_getElem hv,HashInputProgram.clausePayload,literal_payload]
  · exact (H 63 (by decide)).trans (h.blank 63 (by simp))
  · intro i
    exact (H _ (clauseLow_disjoint i)).trans (h.low i)
  · exact (H 69 (by decide)).trans h.one
  · exact (H 76 (by decide)).trans h.minus
  · intro i hi
    exact (H _ (clauseScratch_disjoint i hi)).trans (h.clauseWork i hi)
  · exact fetched_seed regs seed tail f
  · exact (H 159 (by decide)).trans (h.blank 159 (by simp))

end SubexponentialSAT.SqrtLog.LeafProgram.FactorReady

end OAI.Algorithms

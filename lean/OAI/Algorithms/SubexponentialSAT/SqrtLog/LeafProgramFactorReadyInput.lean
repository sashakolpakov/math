import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorReadyTransport
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorReadySize
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorSpec

namespace OAI.Algorithms

/-! One fixed physical invariant for every parsed factor ID. It contains
master bytes and blank scratch, not callback executions or per-ID readiness. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorReady
open SubexponentialSAT BitProgram StructuredCalls MomentsProgram SubexpSetupStorage
open PerturbationAssembly SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native IdempotentApplyProgram.Steps
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev baseData (base : Fin 768 → List Bool) : State 16 768 := ⟨fun _=>false,base⟩

structure Input {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (S A : ℕ) (base : Fin 768 → List Bool) : Prop where
  caller : CallerInput q.p.t q.p.model q.p.modulus q.p.cache q.J q.p.R q.theta (baseData base) n
  physical : SourceReady.Input q.p q.ps q.packing (Incidence.staged (baseData base)) 0 n 0 S
  size : ∀ i,(base i).length ≤ A
  stagedSize : WordBound A (Incidence.staged (baseData base))
  rows : base 701=Encoding.encodeList id q.rawRows
  clauses : base 700=Encoding.encodeList id q.clauses
  count : base 704=List.replicate q.rawRows.length true
  mark : base 705=Encoding.encodeNat q.mark
  flag : base 706=[q.marked]
  dispatchWork : ∀ i ∈ FactorDispatch.scratch,base i=[]
  blank : ∀ i ∈ ([154,63,64,67,68,62,556,684,159] : List (Fin 768)),base i=[]
  hashWidth : (base 708).length=q.bitWidth
  hashModulus : BinaryArithmetic.toNat (base 707)=q.clauses.length
  expand : ∀ i ∈ Expansion.scratch,base i=[]
  work358 : base 358=[]
  work359 : base 359=[]
  low : ∀ i : Fin 56,base (Factor.nativeStacks (Memory.lowPort i))=low q.ctx i
  one : base 69=Product.bytes q.one
  minus : base 76=RingProgram.flat q.minus
  tape : base 143=IdempotentApplyProgram.triplesTape q.digits
  shape : (base 88).length=n
  indicatorWork : ∀ i ∈ FactorServices.indicatorScratch,base (Factor.indicatorStacks i)=[]
  clauseWork : ∀ i ∈ FactorServices.clauseScratch,base (Clause.callerStacks i)=[]

/-- The cap includes the original fixed words, a full Good accumulator, the
unconsumed parser tail, the eligible unary ID, and the fetched payload. -/
def callBound {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A T F : ℕ) : ℕ :=
  wordBound A T (seedBound n (baseWidth 3 q.p.t) d q.u q.J) F
    (payloadBound q.rawRows q.clauses)

structure Limits {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (S A T F : ℕ) : Prop where
  source : sourceCallWordBound (callBound q A T F) n
    (incidenceBitsBound n q.J (d*baseWidth 3 q.p.t)) ≤ S
  live : callBound q A T F ≤ S
  ambient : n ≤ S
  factors : F ≤ S
  plans : (LayoutOwnerFiberProgram.stream q.ps).length ≤ S

variable {r Q n d : ℕ} {q : Factor.Spec r Q n d} {S A : ℕ} {base : Fin 768 → List Bool}

theorem Input.incidence {T F f : ℕ} (h : Input q S A base) (hl : Limits q S A T F)
    (a : State 16 768) (ha : Agree a.stacks base)
    (hf : a.stacks 556=List.replicate f true) (hfid : f ≤ F)
    (hb : WordBound (callBound q A T F) (Incidence.staged a)) :
    IncidenceReady q.p q.ps q.packing q.J n f S (callBound q A T F) q.theta
      a (base 202) (fun _=>[]) := by
  have hc := caller_transfer h.caller ha
  have hs := source_transfer h.physical (staged_agree a (baseData base) ha)
    ((staged_changed a 556 (by decide)).trans hf)
    (fun i=>(hb i).trans hl.live)
  have hw : SourceReady.rawLow (Incidence.staged a) 10=base 202 := by
    change (Incidence.staged a).stacks 350=base 202
    exact (Incidence.staged_copy a hc.destinations_empty (202,350) (by decide)).trans (ha 202 (by decide))
  have out := incidenceReady_of_physical q.p q.ps q.packing q.J n f S (callBound q A T F)
    q.theta a hc ((ha 62 (by decide)).trans (h.blank 62 (by simp)))
    ((ha 684 (by decide)).trans (h.blank 684 (by simp))) hb hl.source hl.ambient
    (hfid.trans hl.factors) hl.plans hs
  simpa only [hw] using out

end SubexponentialSAT.SqrtLog.LeafProgram.FactorReady

end OAI.Algorithms

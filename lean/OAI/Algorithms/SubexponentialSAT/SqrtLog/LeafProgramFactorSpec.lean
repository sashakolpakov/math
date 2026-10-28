import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorCallbackHash
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorCallbackMarked
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorNeutral
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopModel

namespace OAI.Algorithms

/-! Source data and physical premises for the concrete factor callback.
The records below contain no execution hypotheses. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly DensePolynomialProgram NativeSemantics SubexpSetupStorage

structure Spec (r Q n d : ℕ) where
  p : SourceBank.Parameters r Q d
  ps : List (ℕ × ℕ)
  packing : PackingData (Fin ps.length) (UniversalType r Q 1)
  u : ℕ
  J : ℕ
  hu : 0 < u
  hJ : 0 < J
  theta : Coeff (baseWidth 3 p.t) d
  width : List Bool
  widthLength : width.length=baseWidth 3 p.t
  minus : RingProgram.Code (Word (baseWidth 3 p.t)) d
  minusValue : p.ops.decode minus = -1
  one : Raw (p:=3) (t:=p.t) (n:=n) (d:=d)
  oneGood : Good Finset.univ u J one
  oneValue : rawDenote p.ops.decode one=Squarefree.canonical u J 1
  source : List (List (SAT.Literal (Fin n)))
  rows : List (List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3))
  bitWidth : ℕ
  bitWidthPositive : 0 < bitWidth
  sourceBound : 3*(HashInputProgram.Expansion.encodedClauses source).length ≤ 2^bitWidth
  code : RingProgram.Code (RingProgram.ScalarCode 3 p.t) (3*p.t)
  marked : Bool
  mark : ℕ
  markValid : marked=true → mark < source.length

namespace Spec
variable {r Q n d : ℕ} (q : Spec r Q n d)
noncomputable def ctx : Context 3 q.p.t n d := sourceContext q.p n q.u q.J q.width q.widthLength

def rawRows : List (List Bool) := q.rows.map fun ts=>(HashInputProgram.Loop.rawInput q.bitWidth ts).reverse
def clauses : List (List Bool) := HashInputProgram.Expansion.encodedClauses q.source
def markedClause : List (SAT.Literal (Fin n)) := q.source[q.mark]?.getD []
def digits := List.ofFn (IdempotentApplyProgram.coefficientTriple q.p.t q.code)
noncomputable def value (s : Fin 768 → List Bool) (f : ℕ) : Squarefree.Jet (Fin n) (q.p.model.O q.p.t) :=
  if h : f < q.rows.length then
    Semantics.hashValue q.p q.ps q.packing q.u q.J f q.width q.widthLength q.theta s q.source q.rows[f] q.code
  else if q.marked && decide (f=q.rows.length) then
    Semantics.markedValue q.p q.ps q.packing f q.theta s q.markedClause
  else 1
noncomputable def step (s : Fin 768 → List Bool)
    (seed : Raw (p:=3) (t:=q.p.t) (n:=n) (d:=d)) (f : ℕ)
    (out : Raw (p:=3) (t:=q.p.t) (n:=n) (d:=d)) : Prop :=
  rawDenote q.p.ops.decode out=Squarefree.canonical q.u q.J
    (rawDenote q.p.ops.decode seed*q.value s f)

noncomputable def dispatched (a : Data) (f : ℕ) (rd : Fin 8 → Bool) : Data :=
  FactorDispatch.finished a rd q.rawRows q.clauses q.marked q.mark f
end Spec

structure CallInput {r Q n d : ℕ} (q : Spec r Q n d) (S B : ℕ) (a : Data) (f : ℕ)
    (seed : Raw (p:=3) (t:=q.p.t) (n:=n) (d:=d)) : Prop where
  rows : a.stacks 701=Encoding.encodeList id q.rawRows
  clauses : a.stacks 700=Encoding.encodeList id q.clauses
  count : a.stacks 704=List.replicate q.rawRows.length true
  mark : a.stacks 705=Encoding.encodeNat q.mark
  flag : a.stacks 706=[q.marked]
  factor : a.stacks 149=(Encoding.encodeNat f).reverse
  seedBytes : a.stacks 151=MomentsProgram.Product.bytes seed
  dispatchWork : ∀ i ∈ FactorDispatch.scratch,a.stacks i=[]
  blank : ∀ i ∈ ([154,63,64,67,68,62,556] : List (Fin 768)),a.stacks i=[]
  incidence : ∀ rd, IncidenceReady q.p q.ps q.packing q.J n f S B q.theta
    (projectState Incidence.callerRegisters id (FactorID.output (q.dispatched a f rd) f)) (a.stacks 202) (fun _=>[])
  hash : ∀ rd (h : f < q.rows.length), HashInput q.ctx q.minus q.one seed q.source q.rows[f] q.digits q.bitWidth
    (q.dispatched a f rd)
  marked : ∀ rd, q.marked=true → f=q.rows.length → MarkedInput q.ctx q.minus q.one seed q.markedClause
    (q.dispatched a f rd)

structure CallCaps {r Q n d : ℕ} (q : Spec r Q n d) (A B Z D : ℕ) (a : Data) (f : ℕ) : Prop where
  native : FactorBounds.NativeCaps q.ctx Z
  idSize : f ≤ Z
  width : q.bitWidth ≤ Z
  source : (Encoding.encodeList id q.clauses).length ≤ Z
  terms : ∀ ts ∈ q.rows,ts.length ≤ Z
  digits : q.digits.length ≤ Z
  clauseWidths : ∀ ls ∈ q.source,ls.length ≤ Z
  raw : ∀ rd,((q.dispatched a f rd).stacks 154).length ≤ Z
  modulus : ∀ rd,((q.dispatched a f rd).stacks 707).length ≤ Z
  before : ∀ rd, WordBound A (projectState Incidence.callerRegisters id (FactorID.output (q.dispatched a f rd) f))
  staged : ∀ rd, WordBound B (Incidence.staged
    (projectState Incidence.callerRegisters id (FactorID.output (q.dispatched a f rd) f)))
  dispatch : LeafFactorDispatchProgram.budget q.rawRows q.clauses q.mark f ≤ D

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorSpec
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgramModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalarFromCountsDefinitions
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgramModel
import OAI.Algorithms.SubexponentialSAT.Subexp.SelectorProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata
import OAI.Algorithms.SubexponentialSAT.Subexp.CollisionProgram

/-! The attained-tuple traversal retains the actual query inputs and the
meaning of its current pair accumulator. These predicates contain word
identities and algebraic facts, with no execution or algorithm-service fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram Subexp.ConstructivePacking MulticolorTypes
open TruncatedRingProgram SubexpSetupStorage

abbrev Data := State 40 896

/-- Immutable inputs throughout one tuple traversal. Derived per-head words,
the ambient representative baseline869, and the changing accumulator851 are
not members of this list. -/
def masterPorts : List (Fin 896) :=
  [78,128,129,130,131,132,133,134,135,136,138,139,140,141,
   194,201,202,203,204,207,209,211,212,243,256,280,281,
   300,301,302,305,307,320,322,338,640,641,642,647,
   700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,728,
   730,731,732,733,734,735,736,737,738,739,740,741,742,743,
   832,833,834,835,850,857,858,863]

structure QueryMasterFrame (before after : Data) : Prop where
  word : ∀ i∈masterPorts, after.stacks i=before.stacks i

namespace QueryMasterFrame

theorem refl (a : Data) : QueryMasterFrame a a := ⟨fun _ _ => rfl⟩

theorem trans {a b c : Data} (hab : QueryMasterFrame a b) (hbc : QueryMasterFrame b c) :
    QueryMasterFrame a c := ⟨fun i hi => (hbc.word i hi).trans (hab.word i hi)⟩

end QueryMasterFrame

/-- These are the bytes of the genuine factor specification at one generated
node. In particular the lifting cutoff is the ring precision, rather than an
independently chosen positive number. Head buffers are produced inside the
visitor and are not supplied by this predicate. -/
structure QueryReady {r Q n d : ℕ} (q : Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n))
    (P : ℕ) (a : Data) : Prop where
  lifting : q.u=q.p.t
  generatedTheta : q.theta=RingNodeProgram.nodeCode q.p.t d (node.val+1)
  sourceMinus : q.minus=q.p.minusOne
  ambient : a.stacks 128=List.replicate n true
  theta : a.stacks 78=RingProgram.flat q.theta
  modulus : a.stacks 194=q.p.modulus.bits
  table : a.stacks 201=RingTriple.tableEncoding
    (HornerProgram.modelTable q.p.t q.p.model q.p.modulus q.p.cache)
  width : a.stacks 202=q.width
  scalarZero : a.stacks 203=q.p.cache.zero.val
  degree : a.stacks 204=List.replicate d true
  one : a.stacks 207=RingProgram.flat q.p.ops.oneRun.1
  minus : a.stacks 211=RingProgram.flat q.minus
  precision : a.stacks 212=List.replicate q.p.t true
  order : a.stacks 243=List.replicate q.J true
  zero : a.stacks 280=RingProgram.flat q.p.ops.zeroRun.1
  code : a.stacks 281=RingProgram.flat q.code
  clauses : a.stacks 700=Encoding.encodeList id q.clauses
  rows : a.stacks 701=Encoding.encodeList id q.rawRows
  rowCount : a.stacks 704=List.replicate q.rawRows.length true
  markedIndex : a.stacks 705=Encoding.encodeNat q.mark
  markedFlag : a.stacks 706=[q.marked]
  indexModulus : BinaryArithmetic.toNat (a.stacks 707)=q.clauses.length
  indexWidth : (a.stacks 708).length=q.bitWidth
  highMask : a.stacks 702=List.ofFn (fun v : Fin n => decide (v∈H))
  highBits : a.stacks 703=List.ofFn (fun v : Fin n => if h : v∈H then high ⟨v,h⟩ else false)
  outer : a.stacks 858=List.ofFn (fun v : Fin n => decide (v∈E))
  inner : a.stacks 857=List.ofFn (fun v : Fin n => decide (v∈U))
  outerFree : Disjoint E H
  innerSubset : U⊆E
  colors : a.stacks 130=List.replicate r true
  nodes : a.stacks 131=List.replicate Q true
  typeWidth : a.stacks 132=List.replicate (Q*r) true
  positive : a.stacks 710=(LayoutProgramScalar.FromCounts.unsignedSaved q.p.hwords q.p.width q.p.power q.p.R q.p.aWord).hp
  negative : a.stacks 711=(LayoutProgramScalar.FromCounts.unsignedSaved q.p.hwords q.p.width q.p.power q.p.R q.p.aWord).hn
  sourceWidth : a.stacks 140=q.p.width
  power : a.stacks 712=q.p.power.1
  powerNegative : q.p.power.2=[]
  radius : a.stacks 138=List.replicate q.p.R true
  offset : a.stacks 139=q.p.aWord
  metadata : a.stacks 135=OAI.Algorithms.SubexponentialSAT.Subexp.SelectorProgram.rawRecords
    (OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata.records q.packing (fun v => List.replicate v.val true) OAI.Algorithms.SubexponentialSAT.Subexp.CollisionProgram.encodeType)
  plans : a.stacks 136=LayoutOwnerFiberProgram.stream q.ps
  inverses : a.stacks 713=(List.ofFn (fun i : Fin Q => RingProgram.flat (InterpolationCacheProgram.inverseValue q.p.t q.p.model q.p.modulus q.p.cache q.p.minusOne
      (RingNodeProgram.nodeCode q.p.t d (i.val+1))))).flatten
  negatives : a.stacks 714=(List.ofFn (fun i : Fin Q => RingProgram.flat (InterpolationCacheProgram.negativeValue q.p.t q.p.model q.p.modulus q.p.cache q.p.minusOne
      (RingNodeProgram.nodeCode q.p.t d (i.val+1))))).flatten
  differences : a.stacks 715=(List.ofFn (fun i : Fin Q =>
    (List.ofFn (fun j : Fin Q => RingProgram.flat (InterpolationCacheProgram.differenceValue q.p.t q.p.model q.p.modulus q.p.cache q.p.minusOne
      (RingNodeProgram.nodeCode q.p.t d (i.val+1)) (RingNodeProgram.nodeCode q.p.t d (j.val+1))))).flatten)).flatten
  ringWidth : a.stacks 717=q.p.ringWidth
  rowWidth : a.stacks 716=q.p.rowWidth
  inverseDenominator : a.stacks 728=RingProgram.flat q.p.invDenom
  cacheCaps : ∀ p∈LeafNodeCacheProgram.directCopies,
    (a.stacks (p.1.castAdd 128)).length≤P
  ambientCap : (a.stacks 128).length≤P
  oneCap : (a.stacks 207).length≤P

namespace QueryReady

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P : ℕ} {a b : Data}
    (h : QueryReady q node H high E U P a) (hf : QueryMasterFrame a b) :
    QueryReady q node H high E U P b := by
  refine {
    lifting := h.lifting
    generatedTheta := h.generatedTheta
    sourceMinus := h.sourceMinus
    ambient := (hf.word 128 (by decide)).trans h.ambient
    theta := (hf.word 78 (by decide)).trans h.theta
    modulus := (hf.word 194 (by decide)).trans h.modulus
    table := (hf.word 201 (by decide)).trans h.table
    width := (hf.word 202 (by decide)).trans h.width
    scalarZero := (hf.word 203 (by decide)).trans h.scalarZero
    degree := (hf.word 204 (by decide)).trans h.degree
    one := (hf.word 207 (by decide)).trans h.one
    minus := (hf.word 211 (by decide)).trans h.minus
    precision := (hf.word 212 (by decide)).trans h.precision
    order := (hf.word 243 (by decide)).trans h.order
    zero := (hf.word 280 (by decide)).trans h.zero
    code := (hf.word 281 (by decide)).trans h.code
    clauses := (hf.word 700 (by decide)).trans h.clauses
    rows := (hf.word 701 (by decide)).trans h.rows
    rowCount := (hf.word 704 (by decide)).trans h.rowCount
    markedIndex := (hf.word 705 (by decide)).trans h.markedIndex
    markedFlag := (hf.word 706 (by decide)).trans h.markedFlag
    indexModulus := (congrArg BinaryArithmetic.toNat (hf.word 707 (by decide))).trans h.indexModulus
    indexWidth := (congrArg List.length (hf.word 708 (by decide))).trans h.indexWidth
    highMask := (hf.word 702 (by decide)).trans h.highMask
    highBits := (hf.word 703 (by decide)).trans h.highBits
    outer := (hf.word 858 (by decide)).trans h.outer
    inner := (hf.word 857 (by decide)).trans h.inner
    outerFree := h.outerFree
    innerSubset := h.innerSubset
    colors := (hf.word 130 (by decide)).trans h.colors
    nodes := (hf.word 131 (by decide)).trans h.nodes
    typeWidth := (hf.word 132 (by decide)).trans h.typeWidth
    positive := (hf.word 710 (by decide)).trans h.positive
    negative := (hf.word 711 (by decide)).trans h.negative
    sourceWidth := (hf.word 140 (by decide)).trans h.sourceWidth
    power := (hf.word 712 (by decide)).trans h.power
    powerNegative := h.powerNegative
    radius := (hf.word 138 (by decide)).trans h.radius
    offset := (hf.word 139 (by decide)).trans h.offset
    metadata := (hf.word 135 (by decide)).trans h.metadata
    plans := (hf.word 136 (by decide)).trans h.plans
    inverses := (hf.word 713 (by decide)).trans h.inverses
    negatives := (hf.word 714 (by decide)).trans h.negatives
    differences := (hf.word 715 (by decide)).trans h.differences
    ringWidth := (hf.word 717 (by decide)).trans h.ringWidth
    rowWidth := (hf.word 716 (by decide)).trans h.rowWidth
    inverseDenominator := (hf.word 728 (by decide)).trans h.inverseDenominator
    cacheCaps := ?_
    ambientCap := ?_
    oneCap := ?_ }
  · intro p hp
    have hm : p.1.castAdd 128∈masterPorts := by
      simp only [LeafNodeCacheProgram.directCopies,List.mem_cons,
        List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    rw [hf.word _ hm]
    exact h.cacheCaps p hp
  · rw [hf.word 128 (by decide)]
    exact h.ambientCap
  · rw [hf.word 207 (by decide)]
    exact h.oneCap

theorem degree_length {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P : ℕ} {a : Data}
    (h : QueryReady q node H high E U P a) : (a.stacks 204).length=d := by
  rw [h.degree,List.length_replicate]

/-- The generated physical node is interpreted in the same produced ring
used by the native arithmetic and reconstruction. -/
theorem decodedTheta {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P : ℕ} {a : Data}
    (h : QueryReady q node H high E U P a) :
    q.p.ops.decode q.theta=q.p.model.node q.p.t Q q.p.ht q.p.hfield node := by
  rw [h.generatedTheta]
  exact RingNodeProgram.nodeCode_decode q.p.t q.p.ht q.p.hd q.p.model q.p.modulus q.p.cache Q q.p.hfield node

end QueryReady

/-- Inner head and tuple products retain the full dense value. Only the
outer pair accumulator uses the additive marker readout. -/
structure DenseWord {r Q n d : ℕ} (q : Factor.Spec r Q n d) (port : Fin 896)
    (value : Dense (q.p.model.O q.p.t) q.p.t q.J) (a : Data) : Prop where
  entries : ∃ entries : List (Product.Entry n (baseWidth 3 q.p.t) d),
    a.stacks port=Product.bytes entries ∧ Good ∅ q.p.t q.J entries ∧
      rawValue q.p.t q.J q.p.ops.decode entries=value

namespace DenseWord

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {port : Fin 896}
    {value : Dense (q.p.model.O q.p.t) q.p.t q.J} {a b : Data}
    (h : DenseWord q port value a) (hf : b.stacks port=a.stacks port) :
    DenseWord q port value b := by
  obtain ⟨entries,he,hg,hv⟩ := h.entries
  exact ⟨entries,hf.trans he,hg,hv⟩

theorem word_length_le {r Q n d : ℕ} {q : Factor.Spec r Q n d} {port : Fin 896}
    {value : Dense (q.p.model.O q.p.t) q.p.t q.J} {a : Data}
    (h : DenseWord q port value a) :
    (a.stacks port).length≤
      q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2) := by
  obtain ⟨entries,he,hg,_⟩ := h.entries
  rw [he]
  exact empty_bytes_length_le hg

/-- The existing native product uses the actual source-ring table. Its full
dense multiplication law is applied before any additive marker readout. -/
theorem multiplied {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (left right : List (Product.Entry n (baseWidth 3 q.p.t) d))
    (hl : Good ∅ q.p.t q.J left) (hr : Good ∅ q.p.t q.J right)
    (b : Data) (port : Fin 896)
    (hb : b.stacks port=Product.bytes
      (Product.run 3 q.p.t q.p.modulus q.p.cache q.ctx.table q.p.t q.J left right [])) :
    DenseWord q port (rawValue q.p.t q.J q.p.ops.decode left*
      rawValue q.p.t q.J q.p.ops.decode right) b := by
  refine ⟨_,hb,product_good 3 q.p.t q.p.modulus q.p.cache q.ctx.table ∅ q.p.t q.J left right hl hr,?_⟩
  have hv := product_dense 3 q.p.t q.p.modulus q.p.cache
    (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t))
    q.ctx.table (Factor.Semantics.context_table_correct q.p q.u q.J q.width q.widthLength)
    q.p.t q.J left right
  exact hv

end DenseWord

/-- The same actual dictionary supplies the bytes, empty-support storage
bound, and additive readout meaning. No stronger equality of unobserved
lifting-marker coefficients is required. -/
structure PairAccumulatorMeaning {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (value : Truncated (q.p.model.O q.p.t) q.J) (a : Data) : Prop where
  entries : ∃ entries : List (Product.Entry n (baseWidth 3 q.p.t) d),
    a.stacks 851=Product.bytes entries ∧ Good ∅ q.p.t q.J entries ∧
      Dense.readout (rawValue q.p.t q.J q.p.ops.decode entries)=value

namespace PairAccumulatorMeaning

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d}
    {value : Truncated (q.p.model.O q.p.t) q.J} {a b : Data}
    (h : PairAccumulatorMeaning q value a) (hf : b.stacks 851=a.stacks 851) :
    PairAccumulatorMeaning q value b := by
  obtain ⟨entries,he,hg,hv⟩ := h.entries
  exact ⟨entries,hf.trans he,hg,hv⟩

theorem zero {r Q n d : ℕ} (q : Factor.Spec r Q n d) (a : Data)
    (hz : a.stacks 851=[]) : PairAccumulatorMeaning q 0 a := by
  refine ⟨[],?_,Good.nil,?_⟩
  · exact hz
  · rw [rawValue_nil,map_zero]

/-- The retained pair word has a fixed polynomial capacity. This uses the
same witness as its decoded value, and is independent of the number of tuples
already visited. -/
theorem word_length_le {r Q n d : ℕ} {q : Factor.Spec r Q n d}
    {value : Truncated (q.p.model.O q.p.t) q.J} {a : Data}
    (h : PairAccumulatorMeaning q value a) :
    (a.stacks 851).length≤
      q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2) := by
  obtain ⟨entries,he,hg,_⟩ := h.entries
  rw [he]
  exact empty_bytes_length_le hg

/-- Normalization realizes the additive tuple update in the actual produced
ring. The new bytes, validity and meaning all refer to its one output list. -/
theorem normalized {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (seed source : List (Product.Entry n (baseWidth 3 q.p.t) d))
    (hs : Good ∅ q.p.t q.J seed) (ht : Good ∅ q.p.t q.J source)
    (before added : Truncated (q.p.model.O q.p.t) q.J)
    (hbefore : Dense.readout (rawValue q.p.t q.J q.p.ops.decode seed)=before)
    (hadded : Dense.readout (rawValue q.p.t q.J q.p.ops.decode source)=added)
    (b : Data)
    (hb : b.stacks 851=Product.bytes (Normalize.run 3 q.p.t q.p.modulus q.p.cache source seed)) :
    PairAccumulatorMeaning q (before+added) b := by
  refine ⟨_,hb,normalize_good 3 q.p.t q.p.modulus q.p.cache ∅ q.p.t q.J source seed ht.valid hs,?_⟩
  have hv := normalize_dense 3 q.p.t q.p.modulus q.p.cache
    (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t))
    q.p.t q.J source seed hs.nodup
  change rawValue q.p.t q.J q.p.ops.decode
    (Normalize.run 3 q.p.t q.p.modulus q.p.cache source seed)=
      rawValue q.p.t q.J q.p.ops.decode source+rawValue q.p.t q.J q.p.ops.decode seed at hv
  rw [hv,map_add,hadded,hbefore,add_comm]

end PairAccumulatorMeaning

/-- Actual cache initialization changes no retained query input. -/
theorem initialized_masterFrame {a b : Data} {n width d u J : ℕ}
    {one : RingProgram.Code (Word width) d}
    (h : QueryTupleInit.Initialized a b (n:=n) one u J) : QueryMasterFrame a b := by
  constructor
  intro i hi
  apply h.frame i
  simp only [masterPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

/-- Both paid replay initializers preserve every retained query input. -/
theorem replay_masterFrame (a : Data) :
    QueryMasterFrame a (QueryTupleVisitor.tested (QueryTupleVisitor.restartState a)) := by
  constructor
  intro i hi
  have hs : i≠840 ∧ i≠843 := by
    simp only [masterPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact QueryTupleVisitor.restartState_frame a i hs.1 hs.2

/-- The neutral tuple product is decoded from the coefficient word produced
by the ring initializer. It is not a supplied unit dictionary. -/
theorem initialized_unit {r Q n d : ℕ} (q : Factor.Spec r Q n d) {a b : Data}
    (h : QueryTupleInit.Initialized a b (n:=n) q.p.ops.oneRun.1 q.p.t q.J) :
    ∃ entries : List (Product.Entry n (baseWidth 3 q.p.t) d),
      b.stacks 852=Product.bytes entries ∧ Good ∅ q.p.t q.J entries ∧
      rawValue q.p.t q.J q.p.ops.decode entries=1 := by
  refine ⟨FactorAssignmentProgram.oneEntries q.p.ops.oneRun.1,h.unit,
    ⟨h.unit_good.valid,h.unit_good.nodup⟩,?_⟩
  rw [FactorAssignmentProgram.oneEntries_eq_constant _ q.p.t q.J q.p.ht q.hJ]
  exact rawValue_constant_one q.p.t q.J q.p.ops.decode q.p.ops.oneRun.1 q.p.ops.one_correct

/-- The actual tuple initializer restores the fixed retained cap, carries
the current pair sum, and creates the correctly decoded neutral product. -/
theorem initialize_run {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)}
    {P B : ℕ} {a : Data} {value : Truncated (q.p.model.O q.p.t) q.J}
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q value a)
    (ha : WordBound B a) (hPB : 4*P+6≤B) :
    ∃ steps b, Eval QueryTupleInit.command steps a b ∧
      QueryReady q node H high E U P b ∧ PairAccumulatorMeaning q value b ∧
      QueryTupleInit.Initialized a b (n:=n) q.p.ops.oneRun.1 q.p.t q.J ∧
      WordBound B b ∧ steps≤1500*(B+1) ∧
      ∃ entries : List (Product.Entry n (baseWidth 3 q.p.t) d),
        b.stacks 852=Product.bytes entries ∧ Good ∅ q.p.t q.J entries ∧
          rawValue q.p.t q.J q.p.ops.decode entries=1 := by
  have hn : (a.stacks 128).length=n := by rw [hr.ambient,List.length_replicate]
  obtain ⟨steps,b,he,hi,hb,hcost⟩ := QueryTupleInit.command_run a q.p.ops.oneRun.1
    q.p.t q.J P B q.p.ht q.hJ hn hr.one ha hr.cacheCaps hr.ambientCap hr.oneCap hPB
  exact ⟨steps,b,he,hr.frame (initialized_masterFrame hi),
    hm.frame (hi.frame 851 (by decide)),hi,hb,hcost,initialized_unit q hi⟩

/-- The actual tuple-normalization tail preserves the complete retained
input snapshot, including theta78 below the ordinary high-bank frame. -/
theorem finished_masterFrame (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree output : List Bool) :
    QueryMasterFrame a (QueryExecution.TupleEnd.result a rr modulus width degree output) := by
  constructor
  intro i hi
  have hs : i∉SignatureTupleProgram.currentHeadPorts ∧ i≠89 ∧ i≠5 ∧ i≠12 ∧ i≠39 ∧
      i≠851 ∧ i≠852 ∧ i∉QueryTupleSum.scratchPorts :=
    by
      simp only [masterPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
  rw [QueryExecution.TupleEnd.result,QueryExecution.TupleEnd.cleaned,
    QueryTupleInit.cleared_stacks,ite_eq_right hs.1]
  exact QueryTupleSum.result_frame a rr modulus width degree output i hs.2.2.1 hs.2.2.2.1
    hs.2.2.2.2.1 hs.2.1 hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2

/-- The fixed native tail adds the completed tuple's readout to the current
pair sum and returns the same retained capacity. The dense product itself is
kept intact until this addition. -/
theorem finish {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)}
    {P B : ℕ} {a : Data} {value : Truncated (q.p.model.O q.p.t) q.J}
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q value a)
    (source : List (Product.Entry n (baseWidth 3 q.p.t) d))
    (hsource : Good ∅ q.p.t q.J source) (hbytes : a.stacks 852=Product.bytes source)
    (ha : WordBound B a)
    (hcap : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2)≤B) :
    ∃ steps b, Eval QueryExecution.TupleEnd.command steps a b ∧
      QueryReady q node H high E U P b ∧
      PairAccumulatorMeaning q (value+Dense.readout (rawValue q.p.t q.J q.p.ops.decode source)) b ∧
      WordBound B b ∧ QueryMasterFrame a b ∧
      (∀ i∈SignatureTupleProgram.currentHeadPorts,b.stacks i=[]) ∧
      (∀ i,128≤ i.val → i∉SignatureTupleProgram.currentHeadPorts → i≠851 → i≠852 →
        b.stacks i=a.stacks i) ∧
      (∀ i,16≤ i.val → b.regs i=a.regs i) ∧
      steps+1≤QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J B+16*B+25 := by
  obtain ⟨seed,hseed,hgood,hvalue⟩ := hm.entries
  have hready : QueryTupleSum.Ready a q.p.modulus.bits q.width (a.stacks 204)
      (Product.bytes seed) (Product.bytes source) := ⟨hr.modulus,hr.width,rfl,hseed,hbytes⟩
  obtain ⟨steps,rr,he,_,hb,hcost⟩ := QueryExecution.TupleEnd.command_run 3 q.p.t
    q.p.modulus q.p.cache source seed hsource hgood q.width (a.stacks 204)
    hr.degree_length q.widthLength a B ha hready hcap
  refine ⟨steps,_,he,hr.frame (finished_masterFrame ..),?_,hb,finished_masterFrame ..,?_,?_,?_,hcost⟩
  · apply PairAccumulatorMeaning.normalized q seed source hgood hsource value
      (Dense.readout (rawValue q.p.t q.J q.p.ops.decode source)) hvalue rfl
    exact QueryExecution.TupleEnd.result_pair ..
  · intro i hi
    exact QueryExecution.TupleEnd.result_current _ _ _ _ _ _ i hi
  · intro i hi hc h851 h852
    exact QueryExecution.TupleEnd.result_high_frame _ _ _ _ _ _ i hi hc h851 h852
  · intro i hi
    exact QueryExecution.TupleEnd.result_register_frame _ _ _ _ _ _ i hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState

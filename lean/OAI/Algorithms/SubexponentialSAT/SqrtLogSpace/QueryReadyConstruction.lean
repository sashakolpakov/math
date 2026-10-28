import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFactorFields
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryArithmetic
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputPackingTransport

/-! Concrete query-entry facts from the actual arithmetic and native cache
producers. Pair masks are installed by the paid pair-start command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram LeafProgram LeafProgram.PreparedSource
open LeafHeadSetupProgram QueryTupleState
open ProgramTapeReplay
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The cache bootstrap preserves the live source bank exactly. -/
theorem bootstrap_low (s : Native.Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (i : Fin 768) (hi : i.val < 340) :
    (SignatureHeadLoader.bootstrapResult s a ra rd rc words).stacks i = a.stacks i := by
  have hn660 : i ≠ 660 := by intro h; subst i; norm_num at hi
  have hn665 : i ≠ 665 := by intro h; subst i; norm_num at hi
  have he : (SignatureHeadLoader.bootstrapResult s a ra rd rc words).stacks i =
      (Native.start s a ra rd rc words).stacks i := by
    simp only [SignatureHeadLoader.bootstrapResult, Native.start, nodeStart,
      tupleInitialized, Function.update_of_ne hn660, Function.update_of_ne hn665]
  exact he.trans (Native.start_low s a ra rd rc words i hi)

/-- Generated cache bytes and the live master words belong to the same
actual bootstrap endpoint; the old tuple initializer is not invoked. -/
theorem bootstrap_ready (s : Native.Inputs) (a : LeafHeadSetupProgram.Data)
    (ha : Native.Ready s a) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool)
    (words : List (List Bool)) :
    Native.Ready s (SignatureHeadLoader.bootstrapResult s a ra rd rc words) := by
  have hf := bootstrap_low s a ra rd rc words
  obtain ⟨h660,h665⟩ := SignatureHeadLoader.bootstrapResult_markers s a ra rd rc words
  exact ⟨(hf 128 (by decide)).trans ha.ambient,
    (hf 129 (by decide)).trans ha.factors,(hf 130 (by decide)).trans ha.colors,
    (hf 131 (by decide)).trans ha.nodes,(hf 132 (by decide)).trans ha.wordWidth,
    (hf 133 (by decide)).trans ha.words,(hf 134 (by decide)).trans ha.low,
    (hf 135 (by decide)).trans ha.metadata,(hf 136 (by decide)).trans ha.plans,
    (hf 138 (by decide)).trans ha.order,(hf 139 (by decide)).trans ha.height,
    (hf 140 (by decide)).trans ha.width,
    (congrArg BinaryArithmetic.toNat (hf 141 (by decide))).trans ha.offset,
    (hf 307 (by decide)).trans ha.node,h660.trans ha.tuples,h665.trans ha.marker⟩

/-- Paid empty destinations receive precisely the source cache words used
by the genuine factor specification. -/
theorem bootstrap_source_cache (s : Native.Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (h710 : a.stacks 710 = []) (h711 : a.stacks 711 = []) (h712 : a.stacks 712 = []) :
    let b := SignatureHeadLoader.bootstrapResult s a ra rd rc words
    let saved := LayoutProgramScalar.FromCounts.unsignedSaved words s.width s.power s.R s.height
    b.stacks 710 = saved.hp ∧ b.stacks 711 = saved.hn ∧ b.stacks 712 = s.power.1 := by
  dsimp only
  let b := bootState a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words
  have hf (i : Fin 768) (hi : 700 ≤ i.val) : b.stacks i = a.stacks i := by
    apply bootState_frame
    · exact ⟨Or.inr (by omega), by intro he; subst i; norm_num [temporary] at hi⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at *
      intro he
      rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num at hi
  have hp := (retainedState_positive b ((hf 710 (by decide)).trans h710)).trans
    (bootState_positive a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words)
  have hn := (retainedState_negative b ((hf 711 (by decide)).trans h711)).trans
    (bootState_negative a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words)
  have hd := (retainedState_denominator b ((hf 712 (by decide)).trans h712)).trans
    (bootState_denominator a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words)
  refine ⟨hp, ?_, ?_⟩
  · simpa only [SignatureHeadLoader.bootstrapResult, b,
      LayoutProgramScalar.FromCounts.unsignedSaved, unary, List.length_replicate] using hn
  · simpa only [SignatureHeadLoader.bootstrapResult, b, unary, List.length_replicate,
      Native.Inputs.power] using hd

local notation "Hidden" => (fun i : Fin _ =>
  Fin.val i=320 ∨ Fin.val i=322 ∨ Fin.val i=770 ∨ Fin.val i=771 ∨ Fin.val i=781)

def commonPorts : List (Fin 896) :=
  [78,128,130,131,132,135,136,138,139,140,194,201,202,203,204,207,211,212,243,280,281,700,701,702,703,704,705,706,707,708,710,711,712,713,714,715,716,717,728]

theorem commonPorts_visible : ∀ i∈commonPorts, ¬ Hidden i := by
  simp [commonPorts]

/-- Physical query data before a pair is selected. In particular this record
places no condition on either pair-mask destination857/858. -/
structure CommonReady {r Q n d : ℕ} (q : Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (P : ℕ) (a : State 40 896) : Prop where
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
    (a.stacks (p.1.castAdd 128)).length ≤ P
  ambientCap : (a.stacks 128).length ≤ P
  oneCap : (a.stacks 207).length ≤ P

/-- The actual pair start supplies the only four facts absent from the
common physical data. -/
theorem CommonReady.toReady {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H E U : Finset (Fin n)} {high : H → Bool} {P : ℕ} {a : State 40 896}
    (h : CommonReady q node H high P a)
    (hE : a.stacks 858=List.ofFn (fun v : Fin n => decide (v∈E)))
    (hU : a.stacks 857=List.ofFn (fun v : Fin n => decide (v∈U)))
    (hfree : Disjoint E H) (hsub : U⊆E) : QueryReady q node H high E U P a :=
  {h with outer := hE, inner := hU, outerFree := hfree, innerSubset := hsub}

theorem common_of_ready {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H E U : Finset (Fin n)} {high : H → Bool} {P : ℕ} {a : State 40 896}
    (h : QueryReady q node H high E U P a) : CommonReady q node H high P a :=
  {h with}

theorem CommonReady.frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {P : ℕ} {a b : State 40 896}
    (h : CommonReady q node H high P a) (hf : ∀ i∈commonPorts, b.stacks i=a.stacks i) :
    CommonReady q node H high P b := by
  refine {
    lifting := h.lifting
    generatedTheta := h.generatedTheta
    sourceMinus := h.sourceMinus
    ambient := (hf 128 (by decide)).trans h.ambient
    theta := (hf 78 (by decide)).trans h.theta
    modulus := (hf 194 (by decide)).trans h.modulus
    table := (hf 201 (by decide)).trans h.table
    width := (hf 202 (by decide)).trans h.width
    scalarZero := (hf 203 (by decide)).trans h.scalarZero
    degree := (hf 204 (by decide)).trans h.degree
    one := (hf 207 (by decide)).trans h.one
    minus := (hf 211 (by decide)).trans h.minus
    precision := (hf 212 (by decide)).trans h.precision
    order := (hf 243 (by decide)).trans h.order
    zero := (hf 280 (by decide)).trans h.zero
    code := (hf 281 (by decide)).trans h.code
    clauses := (hf 700 (by decide)).trans h.clauses
    rows := (hf 701 (by decide)).trans h.rows
    rowCount := (hf 704 (by decide)).trans h.rowCount
    markedIndex := (hf 705 (by decide)).trans h.markedIndex
    markedFlag := (hf 706 (by decide)).trans h.markedFlag
    indexModulus := (congrArg BinaryArithmetic.toNat (hf 707 (by decide))).trans h.indexModulus
    indexWidth := (congrArg List.length (hf 708 (by decide))).trans h.indexWidth
    highMask := (hf 702 (by decide)).trans h.highMask
    highBits := (hf 703 (by decide)).trans h.highBits
    colors := (hf 130 (by decide)).trans h.colors
    nodes := (hf 131 (by decide)).trans h.nodes
    typeWidth := (hf 132 (by decide)).trans h.typeWidth
    positive := (hf 710 (by decide)).trans h.positive
    negative := (hf 711 (by decide)).trans h.negative
    sourceWidth := (hf 140 (by decide)).trans h.sourceWidth
    power := (hf 712 (by decide)).trans h.power
    powerNegative := h.powerNegative
    radius := (hf 138 (by decide)).trans h.radius
    offset := (hf 139 (by decide)).trans h.offset
    metadata := (hf 135 (by decide)).trans h.metadata
    plans := (hf 136 (by decide)).trans h.plans
    inverses := (hf 713 (by decide)).trans h.inverses
    negatives := (hf 714 (by decide)).trans h.negatives
    differences := (hf 715 (by decide)).trans h.differences
    ringWidth := (hf 717 (by decide)).trans h.ringWidth
    rowWidth := (hf 716 (by decide)).trans h.rowWidth
    inverseDenominator := (hf 728 (by decide)).trans h.inverseDenominator
    cacheCaps := ?_
    ambientCap := ?_
    oneCap := ?_ }
  · intro p hp
    have hm : p.1.castAdd 128∈commonPorts := by
      simp only [LeafNodeCacheProgram.directCopies, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    rw [hf _ hm]
    exact h.cacheCaps p hp
  · rw [hf 128 (by decide)]
    exact h.ambientCap
  · rw [hf 207 (by decide)]
    exact h.oneCap

/-- Erasing the opaque five-word frame cannot change query readiness. -/
theorem ready_rebase {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H E U : Finset (Fin n)} {high : H → Bool} {P : ℕ} {a : State 40 896}
    (h : QueryReady q node H high E U P a) (frame : Fin 896 → List Bool) :
    QueryReady q node H high E U P (rebaseState Hidden frame a) := by
  have hf (i : Fin 896) (hi : ¬ Hidden i) :
      (rebaseState Hidden frame a).stacks i = a.stacks i := ite_eq_right hi
  exact ((common_of_ready h).frame (fun i hi => hf i (commonPorts_visible i hi))).toReady
    ((hf 858 (by decide)).trans h.outer) ((hf 857 (by decide)).trans h.inner)
    h.outerFree h.innerSubset

/-- The source snapshot has the same native readiness after erasing its
opaque collector words; no bound on their old contents is used. -/
theorem native_ready_rebase {s : Native.Inputs} {a : LeafHeadSetupProgram.Data}
    (h : Native.Ready s a) (frame : Fin 768 → List Bool) :
    Native.Ready s (rebaseState Hidden frame a) := by
  have hf (i : Fin 768) (hi : ¬ Hidden i) :
      (rebaseState Hidden frame a).stacks i = a.stacks i := ite_eq_right hi
  exact ⟨(hf 128 (by decide)).trans h.ambient,(hf 129 (by decide)).trans h.factors,
    (hf 130 (by decide)).trans h.colors,(hf 131 (by decide)).trans h.nodes,
    (hf 132 (by decide)).trans h.wordWidth,(hf 133 (by decide)).trans h.words,
    (hf 134 (by decide)).trans h.low,(hf 135 (by decide)).trans h.metadata,
    (hf 136 (by decide)).trans h.plans,(hf 138 (by decide)).trans h.order,
    (hf 139 (by decide)).trans h.height,(hf 140 (by decide)).trans h.width,
    (congrArg BinaryArithmetic.toNat (hf 141 (by decide))).trans h.offset,
    (hf 307 (by decide)).trans h.node,(hf 660 (by decide)).trans h.tuples,
    (hf 665 (by decide)).trans h.marker⟩

/-- Rebase the genuine produced source without retaining an opaque caller
length in its local bound. All semantic/source/cache data are unchanged. -/
def shadowSource (s : SignatureTupleSource.ProducedSource) (B : ℕ)
    (hb : ∀ i, ¬ Hidden i → (s.source.stacks i).length ≤ B) :
    SignatureTupleSource.ProducedSource :=
  {s with source := rebaseState Hidden (fun _ => []) s.source
          ready := native_ready_rebase s.ready _
          bound := B
          bounded := by
            intro i
            change (if Hidden i then [] else s.source.stacks i).length ≤ B
            split_ifs with hi
            · exact Nat.zero_le _
            · exact hb i hi}

/-- Only these actual arithmetic producer outputs are needed at node entry. -/
def arithmeticPorts : List (Fin 768) :=
  [194,201,202,203,204,207,211,212,243,280,281,713,714,715,716,717,728]

/-- Assemble the common physical data for the authentic factor specification
from the actual arithmetic output, native layout masters, bootstrap caches
and frontend words. The frame equations refer to concrete producer states. -/
theorem native_common
    (s : Native.Inputs) (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (words : List (List Bool)) (hc : CacheCorrect s.height (unary s.R) s.width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (base out : State 40 768) (ho : Query.ArithmeticOutput base out m hd M cache half e)
    (hfield : s.Q < 3 ^ (m.val 34)) (hQ : m.val 21 = s.Q)
    (hR : (base.stacks 740).length=s.R) (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (hJ : 0 < m.val 42) (source : List (List (SAT.Literal (Fin s.n))))
    (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (H : Finset (Fin s.n)) (high : H → Bool) (P : ℕ) (a : State 40 896)
    (hnative : Native.Ready s
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hframe : ∀ i∈arithmeticPorts, a.stacks (i.castAdd 128)=out.stacks i)
    (hdegree : out.stacks 204=List.replicate (m.val 34) true)
    (htheta : a.stacks 78=RingProgram.flat
      (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (s.node.val+1)))
    (hpositive : a.stacks 710=(LayoutProgramScalar.FromCounts.unsignedSaved words
      s.width s.power s.R s.height).hp)
    (hnegative : a.stacks 711=(LayoutProgramScalar.FromCounts.unsignedSaved words
      s.width s.power s.R s.height).hn)
    (hpower : a.stacks 712=s.power.1)
    (h700 : a.stacks 700=Encoding.encodeList id q.clauses)
    (h701 : a.stacks 701=HashScopeProgram.RawTable.inputBits q.width.length q.rows)
    (h704 : a.stacks 704=List.replicate q.rows.length true)
    (h705 : a.stacks 705=Encoding.encodeNat (markIndex q))
    (h706 : a.stacks 706=[q.mark.isSome])
    (h707 : a.stacks 707=q.modulus) (h708 : a.stacks 708=q.width)
    (h702 : a.stacks 702=List.ofFn (fun v : Fin s.n => decide (v∈H)))
    (h703 : a.stacks 703=List.ofFn (fun v : Fin s.n => if h:v∈H then high ⟨v,h⟩ else false))
    (hbound : ∀ i ∈ commonPorts, (a.stacks i).length ≤ P) :
    CommonReady (nativeSpecOfInputs s m ht hd words hc M cache half e ho.produced
      hfield q hv (m.val 42) hJ source hsource) s.node H high P a := by
  let spec := nativeSpecOfInputs s m ht hd words hc M cache half e ho.produced
    hfield q hv (m.val 42) hJ source hsource
  have low (i : Fin 640) (hi : i∈([194,201,202,203,207,211,212,243,280,281] : List (Fin 640))) :
      a.stacks ((LeafRingSetupProgram.wideStacks i).castAdd 128)=e.stacks i := by
    have hm : LeafRingSetupProgram.wideStacks i∈arithmeticPorts := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have hl : i.val<340 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    exact (hframe _ hm).trans (ho.low i hl)
  refine {
    lifting := rfl
    generatedTheta := rfl
    sourceMinus := rfl
    ambient := hnative.ambient
    theta := htheta
    modulus := (low 194 (by decide)).trans ho.produced.caches.modulus
    table := (low 201 (by decide)).trans ho.produced.native.table
    width := low 202 (by decide)
    scalarZero := (low 203 (by decide)).trans ho.produced.caches.scalarZero
    degree := (hframe 204 (by decide)).trans hdegree
    one := (low 207 (by decide)).trans ho.produced.caches.fullOne_model
    minus := (low 211 (by decide)).trans
      (ho.produced.caches.fullMinusOne.trans (LeafProgram.Constants.constantCode_flat _ _ _).symm)
    precision := (low 212 (by decide)).trans ho.produced.caches.precision
    order := (low 243 (by decide)).trans ho.produced.jetOrder
    zero := (low 280 (by decide)).trans ho.produced.caches.fullZero_model
    code := (low 281 (by decide)).trans (nativeSpecOfInputs_code s m ht hd words hc M cache
      half e ho.produced hfield q hv (m.val 42) hJ source hsource)
    clauses := ?_
    rows := h701.trans (nativeSpecOfInputs_rows s m ht hd words hc M cache half e
      ho.produced hfield q hv (m.val 42) hJ source hsource).symm
    rowCount := ?_
    markedIndex := h705
    markedFlag := h706
    indexModulus := ?_
    indexWidth := congrArg List.length h708
    highMask := h702
    highBits := h703
    colors := hnative.colors
    nodes := hnative.nodes
    typeWidth := hnative.wordWidth
    positive := hpositive
    negative := hnegative
    sourceWidth := hnative.width
    power := hpower
    powerNegative := rfl
    radius := hnative.order
    offset := hnative.height
    metadata := ?_
    plans := hnative.plans
    inverses := ?_
    negatives := ?_
    differences := ?_
    ringWidth := (hframe 717 (by decide)).trans ho.width
    rowWidth := ?_
    inverseDenominator := ?_
    cacheCaps := ?_
    ambientCap := hbound 128 (by decide)
    oneCap := hbound 207 (by decide) }
  · exact h700.trans (congrArg (Encoding.encodeList id) hsource)
  · change a.stacks 704=List.replicate
      (((castRows (congrArg List.length hsource) q.rows).map
        (fun ts=>(HashInputProgram.Loop.rawInput q.width.length ts).reverse)).length) true
    simpa only [List.length_map,castRows_length] using h704
  · change BinaryArithmetic.toNat (a.stacks 707)=
      (HashInputProgram.Expansion.encodedClauses source).length
    rw [h707,←hsource]
    exact hv.2.2.2.2.2.1
  · change a.stacks 135=OAI.Algorithms.SubexponentialSAT.Subexp.SelectorProgram.rawRecords
      (OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata.records
        (PackingIncidenceInput.reindexPacking s.plans_length.symm s.packing)
        (fun v=>List.replicate v.val true) OAI.Algorithms.SubexponentialSAT.Subexp.CollisionProgram.encodeType)
    rw [PackingIncidenceInput.reindexPacking_metadataBytes]
    exact hnative.metadata
  · refine (hframe 713 (by decide)).trans ?_
    rw [ho.inverse,hQ]
    exact LayoutProgram.SourceBank.Parameters.inverseBytes_eq spec.p
  · refine (hframe 714 (by decide)).trans ?_
    rw [ho.negative,hQ]
    exact LayoutProgram.SourceBank.Parameters.negativeBytes_eq spec.p
  · refine (hframe 715 (by decide)).trans ?_
    rw [ho.difference,hQ]
    exact LayoutProgram.SourceBank.Parameters.differenceBytes_eq spec.p
  · refine (hframe 716 (by decide)).trans ?_
    rw [ho.nodesLength,hQ]
    rfl
  · refine (hframe 728 (by decide)).trans ?_
    rw [ho.denominator,hR]
    rfl
  · intro p hp
    apply hbound
    simp only [LeafNodeCacheProgram.directCopies, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- The pair expander changes only its masks, cleared accumulator and private
scratch, all disjoint from the common source data. -/
theorem CommonReady.pair_frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {P : ℕ} {a b : State 40 896}
    (h : CommonReady q node H high P a)
    (hf : ∀ i, i∉PairNativeSetup.scratch → i≠851 → i≠857 → i≠858 →
      b.stacks i=a.stacks i) : CommonReady q node H high P b := by
  apply h.frame
  intro i hi
  have hp : ∀ j∈commonPorts,
      j∉PairNativeSetup.scratch ∧ j≠851 ∧ j≠857 ∧ j≠858 := by
    simp [commonPorts,PairNativeSetup.scratch]
  exact hf i (hp i hi).1 (hp i hi).2.1 (hp i hi).2.2.1 (hp i hi).2.2.2

/-- A generated residual support contains only ambient free coordinates. -/
theorem expanded_disjoint {n : ℕ} (H : Finset (Fin n)) (E : Finset (Fin (n-H.card))) :
    Disjoint (E.image (fun i => (HighIncidenceProgram.freeOrder H i).val)) H := by
  rw [Finset.disjoint_left]
  intro v hv hH
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
  exact (HighIncidenceProgram.freeOrder H i).property hH

/-- The fixed paid pair-start command instantiates readiness from emitted
ternary masks. Both initially blank and arbitrary old mask words are allowed. -/
theorem pair_start_ready {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    (H : Finset (Fin n)) (high : H → Bool) (P B : ℕ) (a : State 40 896)
    (h : CommonReady q node H high P a)
    (E U : Finset (Fin (n-H.card))) (hU : U⊆E)
    (hm : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (he : a.stacks 834=((DifferencePairs.encodePair E U).map Option.isSome).reverse)
    (hu : a.stacks 835=((DifferencePairs.encodePair E U).map (fun x => x.getD false)).reverse)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, Eval QueryExecution.PairStart.command steps a b ∧ b.stacks 851=[] ∧
      QueryReady q node H high
        (E.image (fun i => (HighIncidenceProgram.freeOrder H i).val))
        (U.image (fun i => (HighIncidenceProgram.freeOrder H i).val)) P b ∧
      (∀ i, (b.stacks i).length ≤ B) ∧ steps + 1 ≤ 300 * (B + n + 1) + 2 * B + 5 ∧
      ∀ (k : ℕ) z, k ≤ steps + 1 → Trace QueryExecution.PairStart.program k
        (a.withPC (some QueryExecution.PairStart.program.entry)) z →
        ∀ i,(z.stacks i).length≤896*B+(300*(B+n+1)+2*B+5) := by
  obtain ⟨steps,b,hr,hzero,hE,hI,_hs,hf,hb',ht⟩ :=
    QueryExecution.PairStart.support_command_run a H E U hU B hm he hu hb
  refine ⟨steps,b,hr,hzero,(h.pair_frame hf).toReady hE hI
    (expanded_disjoint H E) (Finset.image_subset_image hU),hb',ht,?_⟩
  have hin : dataBits (a.withPC (some QueryExecution.PairStart.program.entry))≤896*B :=
    StreamResources.dataBits_le_mul _ hb
  intro k z hk hz i
  exact StructuredSpace.local_stack_bound QueryExecution.PairStart.program hin k z
    (hk.trans ht) hz i

/-- The native bootstrap dimension is generated from the actual plan stream. -/
theorem native_start_dimension (s : Native.Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    (Native.start s a ra rd rc words).stacks 647=List.replicate s.records.length true := by
  unfold Native.start nodeStart
  simp only [tupleInitialized,Function.update_of_ne (show (647:Fin 768)≠665 by decide),
    Function.update_of_ne (show (647:Fin 768)≠660 by decide)]
  rw [retainedState_frame _ 647 (by decide) (by decide) (by decide) (by decide)]
  exact bootState_dimension _ _ _ _ _ _ _ _ _ _ _

/-- Rebasing the source snapshot preserves every actual native loader master,
including the four words generated by the bootstrap. -/
theorem shadowSource_masters (s : SignatureTupleSource.ProducedSource) (B : ℕ)
    (hb : ∀ i, ¬ Hidden i → (s.source.stacks i).length ≤ B) :
    SignatureHeadLoader.MasterFrame s.masters (shadowSource s B hb).masters := by
  have low (i : Fin 768) (hi : i.val<340)
      (hv : ¬ Hidden i) : (shadowSource s B hb).masters.stacks i=s.masters.stacks i := by
    change (Native.start s.input (rebaseState Hidden (fun _=>[]) s.source)
        s.addressRegisters s.dimensionRegisters s.cacheRegisters s.cacheWords).stacks i=
      (Native.start s.input s.source s.addressRegisters s.dimensionRegisters
        s.cacheRegisters s.cacheWords).stacks i
    rw [Native.start_low _ _ _ _ _ _ _ hi,Native.start_low _ _ _ _ _ _ _ hi]
    exact ite_eq_right hv
  constructor
  intro i hi
  simp only [SignatureHeadLoader.masters, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact (Native.start_positive s.input _ s.addressRegisters s.dimensionRegisters
      s.cacheRegisters s.cacheWords).trans
        (Native.start_positive s.input s.source s.addressRegisters s.dimensionRegisters
          s.cacheRegisters s.cacheWords).symm
  · exact (Native.start_negative s.input _ s.addressRegisters s.dimensionRegisters
      s.cacheRegisters s.cacheWords).trans
        (Native.start_negative s.input s.source s.addressRegisters s.dimensionRegisters
          s.cacheRegisters s.cacheWords).symm
  · exact (Native.start_denominator s.input _ s.addressRegisters s.dimensionRegisters
      s.cacheRegisters s.cacheWords).trans
        (Native.start_denominator s.input s.source s.addressRegisters s.dimensionRegisters
          s.cacheRegisters s.cacheWords).symm
  · exact (native_start_dimension s.input _ s.addressRegisters s.dimensionRegisters
      s.cacheRegisters s.cacheWords).trans
        (native_start_dimension s.input s.source s.addressRegisters s.dimensionRegisters
          s.cacheRegisters s.cacheWords).symm

/-- The caller and source snapshot can be rebased together without any old
opaque-word cap. The loader sees precisely the same native master bytes. -/
theorem shadowSource_caller_frame (s : SignatureTupleSource.ProducedSource) (B : ℕ)
    (hb : ∀ i, ¬ Hidden i → (s.source.stacks i).length ≤ B) (a : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    SignatureHeadLoader.MasterFrame (shadowSource s B hb).masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks
        (rebaseState Hidden (fun _=>[]) a)) := by
  constructor
  intro i hi
  have hv : ∀ j∈SignatureHeadLoader.masters, ¬ Hidden (SignatureHeadLoader.lowStacks j) := by
    simp [SignatureHeadLoader.masters,SignatureHeadLoader.lowStacks,Fin.castAddEmb,Fin.castLEEmb]
  have he : (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks
      (rebaseState Hidden (fun _=>[]) a)).stacks i=
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a).stacks i :=
    ite_eq_right (hv i hi)
  exact he.trans ((hm.stored i hi).trans ((shadowSource_masters s B hb).stored i hi).symm)

/-- A joint replacement preserves the full query-master relation, even when
both states retain collector tapes in that relation. -/
theorem queryMasterFrame_rebase {a b : State 40 896}
    (h : QueryMasterFrame a b) (K : Fin 896 → Prop) [DecidablePred K]
    (frame : Fin 896 → List Bool) :
    QueryMasterFrame (rebaseState K frame a) (rebaseState K frame b) := by
  constructor
  intro i hi
  change (if K i then frame i else b.stacks i)=(if K i then frame i else a.stacks i)
  by_cases hk : K i
  · rw [ite_eq_left hk, ite_eq_left hk]
  · simpa only [ite_eq_right hk] using h.word i hi

section SharedSource

variable (src : SignatureTupleSource.ProducedSource)
    (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : src.input.Q < 3 ^ (m.val 34)) (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (hJ : 0 < m.val 42) (source : List (List (SAT.Literal (Fin src.input.n))))
    (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)

/-- One source snapshot supplies the native input and generated cache of the
factor specification. There is no second, independently chosen input record. -/
noncomputable def sourceSpec : Factor.Spec src.input.r src.input.Q src.input.n (m.val 34) :=
  nativeSpecOfInputs src.input m ht hd src.cacheWords src.cache M cache half e hp
    hfield q hv (m.val 42) hJ source hsource

local notation "spec" => sourceSpec src m ht hd M cache half e hp hfield q hv hJ source hsource

/-- These literal projections expose the shared addressed-input provenance
needed by produced-rank/source alignment, including its actual dimension. -/
theorem sourceSpec_provenance :
    (spec).ps=src.input.plans ∧ (spec).ps=List.ofFn src.plans ∧
    (spec).ps.length=src.input.D ∧
    (spec).packing=PackingIncidenceInput.reindexPacking src.input.plans_length.symm src.input.packing ∧
    (spec).p.hwords=src.cacheWords ∧ (spec).p.R=src.input.R ∧ (spec).p.width=src.input.width ∧
    (spec).p.aWord=src.input.height ∧ (spec).p.power=src.input.power ∧
    (spec).theta=RingNodeProgram.nodeCode (m.val 33) (m.val 34) (src.input.node.val+1) ∧
    (spec).source=source ∧ (spec).u=m.val 33 ∧ (spec).J=m.val 42 :=
  ⟨rfl,src.plans_eq,src.input.plans_length,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Erasing the source-only opaque frame does not change the authentic factor
specification, its ring, node, source, owner plans or cache words. -/
theorem sourceSpec_shadow (B : ℕ)
    (hb : ∀ i, ¬ Hidden i → (src.source.stacks i).length ≤ B) :
    sourceSpec (shadowSource src B hb) m ht hd M cache half e hp hfield q hv hJ source hsource=spec := rfl

end SharedSource

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction

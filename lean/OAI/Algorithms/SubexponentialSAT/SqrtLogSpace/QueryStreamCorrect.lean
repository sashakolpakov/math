import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeLoopSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySourceBank
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeMetadata
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryDecode
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryCountReconstruction
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame

/-! Physical boundaries of the fixed conditioned query. The node invariant
retains the actual prepared words and the exact length of the emitted stream;
it contains no execution or evaluator fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open SubexpSetupStorage

abbrev Data := State 40 896

/-- The measured polynomial prefix precedes every actual pair traversal. -/
def prepareBudget (A : ℕ) : ℕ :=
  20000*(QueryHeadBudgets.compact A+1)^4+300*(QueryHeadBudgets.compact A+1)

def finishBudget (n t d J A : ℕ) : ℕ :=
  QueryNodeFinish.budget n (baseWidth 3 t) d t J (QueryHeadBudgets.compact A)

/-- `work` is the original assembled query resource, instantiated below by
the addressed packing. Its square pays the actual pair and tuple iterator. -/
def nodeBudget (n t d J A work : ℕ) : ℕ :=
  prepareBudget A+StreamedQueryMeasuredCost.pairCoefficient A*work^2+10+
    finishBudget n t d J A

/-- Includes actual high decoding, cursor initialization, every node and the
full canonical reconstruction with its final halt. -/
def budget (n t d Q J A S work : ℕ) : ℕ :=
  18*QueryHeadBudgets.compact A+65*n+67+23*QueryHeadBudgets.compact A+
    Q*(nodeBudget n t d J A work+1)+32+
    QueryReconstruction.budget (QueryHeadBudgets.compact A) S

def nodeSpace (n t d J A : ℕ) : ℕ :=
  max (StreamedQueryMeasuredCost.pairSpaceEnvelope A)
    (896*QueryHeadBudgets.compact A+prepareBudget A+finishBudget n t d J A+1)

def space (n t d J A S : ℕ) : ℕ :=
  max (67*QueryHeadBudgets.compact A+37)
    (max (max (919*QueryHeadBudgets.compact A+31) (nodeSpace n t d J A))
      (896*QueryHeadBudgets.compact A+QueryReconstruction.budget (QueryHeadBudgets.compact A) S))

def retainedPorts : List (Fin 896) :=
  QueryNodeEvaluation.framePorts.filter (fun i => i≠307 ∧ i≠863)

/-- These are the immutable prepared inputs between interpolation nodes.
The node index and the growing coefficient stream have separate exact fields. -/
structure NodeBoundary (initial : Data) (t d Q J B index : ℕ) (a : Data) : Prop where
  cursor : a.stacks 301=Encoding.encodeList id ((RingNodeMetadata.nodeBits t d Q).drop index)
  node : a.stacks 307=List.replicate index true
  guard : a.regs 37= !((RingNodeMetadata.nodeBits t d Q).drop index).isEmpty
  retained : ∀ i∈retainedPorts,a.stacks i=initial.stacks i
  stream_length : (a.stacks 863).length=index*(J*(d*baseWidth 3 t))
  readout_scratch : (0 : ℕ) < index → a.stacks 89=[]
  bounded : WordBound B a

/-- The actual paid initializer establishes the zero-node boundary from the
producer's framed table, including the empty unframed coefficient stream. -/
theorem initialized_boundary (a : Data) (t d Q J B : ℕ)
    (hn : a.stacks 300=Encoding.encodeList id (RingNodeMetadata.nodeBits t d Q))
    (hb : WordBound B a) :
    NodeBoundary a t d Q J B 0
      (QueryNodeFinish.guarded (QueryAssembler.Nodes.initialized a)) := by
  obtain ⟨hcursor,hnode,hstream,hguard,_,hbound⟩ :=
    QueryNodeLoopSpace.initialized_boundary a (RingNodeMetadata.nodeBits t d Q) B hn hb
  refine ⟨by simpa using hcursor,hnode,by simpa using hguard,?_,?_,?_,hbound⟩
  · intro i hi
    apply QueryNodeLoopSpace.initialized_frame a i
    intro hbad
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hbad
    rcases hbad with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [retainedPorts,QueryNodeEvaluation.framePorts] at hi
  · simp [hstream]
  · omega


/-- The actual parked layout remains the source of every node's addressed
input. The loop changes only the unary node index in this readback. -/
theorem NodeBoundary.sourceBank
    (query : LeafQueryFrontend.Query) (k : ℕ)
    (hg : LeafParametersProgram.Guard (query.input k))
    (base front : State 40 768) (lengths : Fin 8 → ℕ)
    (bw : LeafParametersProgram.Bank.Words)
    (hf : LeafProgram.Query.FrontState query k base front lengths bw)
    (first : MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
      (LeafProgram.Query.packingProblem query k hg).Q)
    (tail : List (MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
      (LeafProgram.Query.packingProblem query k hg).Q))
    (node : Fin (LeafProgram.Query.packingProblem query k hg).Q)
    {initial a : Data} {t d Q J B : ℕ}
    (h : NodeBoundary initial t d Q J B node.val a)
    (hpark : ∀ i : Fin 14,
      initial.stacks (NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high i)) =
        (PackingCallerProgram.result front (LeafProgram.Query.packingProblem query k hg)
          first tail).stacks (LeafProgram.LayoutMasters.high i)) :
    NativeLayoutLoad.SourceBank
      (LeafHeadSetupProgram.Native.queryInputsAddressed query k hg first tail node) a := by
  apply NativeQueryPreparation.sourceBank_of_parked query k hg base front lengths bw hf
    first tail node a
  · intro i
    have hi : NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high i)∈retainedPorts := by
      fin_cases i <;> decide
    exact (h.retained _ hi).trans (hpark i)
  · exact h.node

/-- The bytes returned by the actual node readout advance the stream length
by exactly J full scalar words. No uniqueness of their encodings is used. -/
theorem NodeBoundary.next {initial a b : Data} {t d Q J B index : ℕ}
    (h : NodeBoundary initial t d Q J B index a)
    (codes : List (DensePolynomialProgram.Coeff (baseWidth 3 t) d))
    (hlen : codes.length=J)
    (hcursor : b.stacks 301=Encoding.encodeList id
      ((RingNodeMetadata.nodeBits t d Q).drop (index+1)))
    (hnode : b.stacks 307=List.replicate (index+1) true)
    (hguard : b.regs 37= !((RingNodeMetadata.nodeBits t d Q).drop (index+1)).isEmpty)
    (hframe : ∀ i∈retainedPorts,b.stacks i=a.stacks i)
    (hstream : b.stacks 863=a.stacks 863++(codes.map RingProgram.flat).flatten)
    (hscratch : b.stacks 89=[]) (hb : WordBound B b) :
    NodeBoundary initial t d Q J B (index+1) b := by
  refine ⟨hcursor,hnode,hguard,fun i hi=>(hframe i hi).trans (h.retained i hi),?_,
    fun _=>hscratch,hb⟩
  rw [hstream,List.length_append,h.stream_length]
  have hc : ((codes.map RingProgram.flat).flatten).length=J*(d*baseWidth 3 t) := by
    change (DensePolynomialProgram.encode codes).length=_
    simp [hlen]
  rw [hc]
  ring

/-- Fresh per-node cache and parked-input caps are inherited from the
immutable produced words, independently of larger scratch at a loop boundary. -/
theorem NodeBoundary.input_caps {initial a : Data} {t d Q J B index A : ℕ}
    (h : NodeBoundary initial t d Q J B index a)
    (hcache : ∀ i∈QueryNodeEvaluation.cacheInputPorts,(initial.stacks i).length≤A)
    (hparked : ∀ i : Fin 14,
      (initial.stacks (NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high i))).length≤A) :
    (∀ i∈QueryNodeEvaluation.cacheInputPorts,(a.stacks i).length≤A) ∧
    (∀ i : Fin 14,
      (a.stacks (NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high i))).length≤A) := by
  constructor
  · intro i hi
    have hm : i∈retainedPorts := by
      simp only [QueryNodeEvaluation.cacheInputPorts, List.mem_cons,
        List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    rw [h.retained i hm]
    exact hcache i hi
  · intro i
    have hm : NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high i)∈retainedPorts := by
      fin_cases i <;> decide
    rw [h.retained _ hm]
    exact hparked i

theorem NodeBoundary.arithmetic {initial a : Data} {t d Q J B index : ℕ}
    (h : NodeBoundary initial t d Q J B index a) (out : State 40 768)
    (hf : ∀ i∈QueryReadyConstruction.arithmeticPorts,
      initial.stacks (i.castAdd 128)=out.stacks i) :
    ∀ i∈QueryReadyConstruction.arithmeticPorts,a.stacks (i.castAdd 128)=out.stacks i := by
  intro i hi
  have hm : i.castAdd 128∈retainedPorts := by
    simp only [QueryReadyConstruction.arithmeticPorts, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact (h.retained _ hm).trans (hf i hi)

/-- The global fixed stream capacity pays for the next complete node, even
when its coefficient words encode zero. -/
theorem NodeBoundary.room {initial a : Data} {t d Q J B index : ℕ}
    (h : NodeBoundary initial t d Q J B index a) (hi : index<Q)
    (hQ : Q≤B) (hstream : Q*(J*(d*baseWidth 3 t))≤B) :
    (a.stacks 863).length+J*(d*baseWidth 3 t)≤B ∧ index+1≤B := by
  constructor
  · rw [h.stream_length]
    calc
      index*(J*(d*baseWidth 3 t))+J*(d*baseWidth 3 t) =
          (index+1)*(J*(d*baseWidth 3 t)) := by ring
      _ ≤ Q*(J*(d*baseWidth 3 t)) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ B := hstream
  · omega

/-- Compose the actual decoder, ordered node execution and reconstruction.
The three independently established space caps combine by maximum. -/
theorem command_eval_prefix {np nn nr Dp Dn Dr : ℕ} {a b c out : Data}
    (hp : Eval HighQueryAdapter.prepareHigh np a b)
    (hn : Eval QueryStreamProgram.nodes nn b c)
    (hr : Eval QueryReconstruction.command nr c out)
    (sp : QueryExecution.PrefixBound HighQueryAdapter.prepareHigh (np+1) a Dp)
    (sn : QueryExecution.PrefixBound QueryStreamProgram.nodes (nn+1) b Dn)
    (sr : QueryExecution.PrefixBound QueryReconstruction.command (nr+1) c Dr) :
    Eval QueryStreamProgram.command (np+nn+nr) a out ∧
      Trace QueryStreamProgram.program (np+nn+nr+1)
        (a.withPC (some QueryStreamProgram.program.entry)) (out.withPC none) ∧
      QueryExecution.PrefixBound QueryStreamProgram.command (np+nn+nr+1) a
        (max Dp (max Dn Dr)) := by
  have ep : QueryExecution.PrefixBound HighQueryAdapter.prepareHigh np a
      (max Dp (max Dn Dr)) := ⟨fun k z hk hz i =>
    (sp.bound k z (by omega) hz i).trans (Nat.le_max_left _ _)⟩
  have en : QueryExecution.PrefixBound QueryStreamProgram.nodes nn b
      (max Dp (max Dn Dr)) := ⟨fun k z hk hz i =>
    (sn.bound k z (by omega) hz i).trans
      ((Nat.le_max_left Dn Dr).trans (Nat.le_max_right _ _))⟩
  have er : QueryExecution.PrefixBound QueryReconstruction.command nr c
      (max Dp (max Dn Dr)) := ⟨fun k z hk hz i =>
    (sr.bound k z (by omega) hz i).trans
      ((Nat.le_max_right Dn Dr).trans (Nat.le_max_right _ _))⟩
  have he : Eval QueryStreamProgram.command (np+nn+nr) a out := by
    simpa only [QueryStreamProgram.command,Nat.add_assoc] using hp.seq (hn.seq hr)
  have hs := QueryExecution.prefix_seq hp (hn.seq hr) ep
    (QueryExecution.prefix_seq hn hr en er)
  refine ⟨he,compiled_halt_trace he 330 323,⟨?_⟩⟩
  apply StructuredSpace.compiled_halt_stack_bound he 838 838
  simpa only [QueryStreamProgram.command,Nat.add_assoc] using hs.bound

section ActualNode
open LeafParametersProgram LeafProgram LeafProgram.PreparedSource LeafHeadSetupProgram
open QueryNodeEvaluation

variable (query : LeafQueryFrontend.Query) (k RB RC RD RI RE : ℕ)
  (hg : Guard (query.input k)) (hv : query.Valid)
  (first : MulticolorTypes.Word (Query.packingProblem query k hg).r
    (Query.packingProblem query k hg).Q)
  (tail : List (MulticolorTypes.Word (Query.packingProblem query k hg).r
    (Query.packingProblem query k hg).Q))
  (node : Fin (Query.packingProblem query k hg).Q)
  (m : Circuit.Model) (padding : Fin 8 → ℕ)
  (hm : m=Execute.guardedModel (query.input k) padding)
  (ht : 0 < m.val 33) (hd : 0 < m.val 34)
  (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
  (cache : RingProgram.ScalarCache 3 (m.val 33))
  (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
  (base out : State 40 768) (ho : Query.ArithmeticOutput base out m hd M cache half e)
  (hfield : (Native.queryInputsAddressed query k hg first tail node).Q < 3 ^ (m.val 34))
  (hQ : m.val 21=(Native.queryInputsAddressed query k hg first tail node).Q)
  (hR : (base.stacks 740).length=(Native.queryInputsAddressed query k hg first tail node).R)
  (hJ : 0 < m.val 42)
  (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed query k hg first tail node).n))))
  (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source)
local notation "native" => Native.queryInputsAddressed query k hg first tail node
local notation "H" => HighMarkedFrontend.highSet query
local notation "resources" => ProducedQueryResources.ofPacking query k RB RC RD RI RE hg first tail
local notation "work" => CostAssembly.assembledWork k (ProducedQueryResources.ambient query) resources
local notation "bits" => RingProgram.flat (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (node.val+1))

include hm hQ hR in
/-- One actual node executes its preparation, complete pair/tuple traversal
and coefficient readout. Every numerical and semantic source premise is
constructed from the same physical input and actual produced ring. -/
theorem node_run (high : H → Bool) (A : ℕ) (a : State 40 896)
    (remaining : List (List Bool))
    (hbank : NativeLayoutLoad.SourceBank native a)
    (hparked : ∀ j : Fin 14,
      (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length≤A)
    (hcache : ∀ i∈cacheInputPorts,(a.stacks i).length≤A)
    (hvalues : ∀ i,m.val i≤A)
    (hsources : Query.Sources query (projectState (id : Fin 40 → Fin 40) QueryAssembler.Nodes.lowPort a))
    (h700 : (a.stacks 700).length≤A) (h701 : (a.stacks 701).length≤A)
    (h708 : (a.stacks 708).length≤A)
    (hcursor : a.stacks 301=Encoding.encodeList id (bits::remaining))
    (hmask : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (hframe : ∀ i∈QueryReadyConstruction.arithmeticPorts,a.stacks (i.castAdd 128)=out.stacks i)
    (hdegree : out.stacks 204=List.replicate (m.val 34) true)
    (h704 : a.stacks 704=List.replicate query.rows.length true)
    (h705 : a.stacks 705=Encoding.encodeNat (markIndex query))
    (h706 : a.stacks 706=[query.mark.isSome])
    (h702 : a.stacks 702=List.ofFn
      (fun v : Fin (BinaryArithmetic.toNat query.ambient) => decide (v ∈ H)))
    (h703 : a.stacks 703=List.ofFn
      (fun v : Fin (BinaryArithmetic.toNat query.ambient) =>
        if h : v ∈ H then high ⟨v, h⟩ else false))
    (ha : WordBound (QueryHeadBudgets.compact A) a)
    (hout : (a.stacks 863).length+(m.val 42)*((m.val 34)*baseWidth 3 (m.val 33))≤QueryHeadBudgets.compact A) :
    ∃ words, ∃ hc : CacheCorrect (native).height (unary (native).R) (native).width words,
    ∃ steps z, ∃ codes : List (DensePolynomialProgram.Coeff (baseWidth 3 (m.val 33)) (m.val 34)),
      let factor := nativeSpecOfInputs native m ht hd words hc M cache half e ho.produced
        hfield query hv (m.val 42) hJ source hsource
      Eval QueryStreamProgram.nodeBody steps a z ∧ codes.length=m.val 42 ∧
      codes.map factor.p.ops.decode=List.ofFn
        (Truncated.ofPolynomial (m.val 42) ((NodeConcrete.specTarget factor H high).comp
          (Polynomial.X+Polynomial.C (factor.p.ops.decode factor.theta)))).coeff ∧
      z.stacks 863=a.stacks 863++(codes.map RingProgram.flat).flatten ∧
      z.stacks 301=Encoding.encodeList id remaining ∧
      z.stacks 307=List.replicate (node.val+1) true ∧
      z.regs 37= !remaining.isEmpty ∧ z.regs 38=true ∧ z.stacks 89=[] ∧
      (∀ i∈framePorts,i≠307 → i≠863 → z.stacks i=a.stacks i) ∧
      WordBound (QueryHeadBudgets.compact A) z ∧
      steps≤nodeBudget (native).n (m.val 33) (m.val 34) (m.val 42) A work ∧
      QueryExecution.PrefixBound QueryStreamProgram.nodeBody (steps+1) a
        (nodeSpace (native).n (m.val 33) (m.val 34) (m.val 42) A) := by
  let F := QueryHeadBudgets.compact A
  let physical := QuerySourceSnapshot.snapshot (sourceSnapshot a bits remaining)
  have ready : Native.Ready native physical := QuerySourceSnapshot.snapshot_ready
    (sourceSnapshot_ready native a bits remaining hbank)
  have bounded : WordBound A physical := QuerySourceSnapshot.snapshot_bound _ A
    (sourceSnapshot_bank_bound native a bits remaining A hbank hparked)
  have hcap : SignatureHeadLoader.bootstrapOutputBound native≤F :=
    QueryNodeSourceBounds.bootstrap_capacity_of_ready native physical A ready bounded
  obtain ⟨ra,rd,rc,words,hc,np,b,hp,hpt,hb,hcommon,hzero,_hpair,h832,h833,h834,h835,
      h301,_h307,h863,hbf,_hready,_hsnap,hmast,haddress,_htrace,_hpref⟩ :=
    prepare_native_run native m ht hd M cache half e base out ho hfield hQ hR query hv hJ
      source hsource H high F a hbank remaining hcursor hmask hframe hdegree
      hsources.formula hsources.rows h704 h705 h706 hsources.modulus hsources.width
      h702 h703 ha hcap
  let src := nodeSource query k hg first tail node a bits remaining A hbank hparked ra rd rc words hc
  let factor := QueryReadyConstruction.sourceSpec src m ht hd M cache half e ho.produced
    hfield query hv hJ source hsource
  have common : QueryReadyConstruction.CommonReady factor node H high A b :=
    prepared_common_cache_bound hcommon hbf hbank.ambient hcache
  have caps := QueryNodeSourceBounds.headBounds query k hg first tail node a bits remaining A
    hbank hparked ra rd rc words hc m ht hd M cache half e ho.produced hfield hv hJ
    source hsource hvalues hsources h700 h701 h708
  have cap := QueryNodeSourceBounds.retainedCap query k hg first tail node a bits remaining A
    hbank hparked ra rd rc words hc
  have hheads : ∀ depth<(native).r,src.headSize depth≤(resources).headSize := by
    intro depth hdepth
    exact StreamedQueryMeasuredCost.addressed_headSize query k RB RC RD RI RE hg first tail node
      physical ready A bounded ra rd rc words hc depth hdepth
  have hnodeCap := QueryNodeSourceBounds.node_capacity query k hg first tail node a bits remaining A
    hbank hparked ra rd rc words hc m ht hd M cache half e ho.produced hfield hv hJ
    source hsource hvalues
  have hnext : node.val+1≤F := by
    have hn : node.val<(native).Q := node.isLt
    have hq : (native).Q≤F := hnodeCap.2
    omega
  have hcurrentMask : b.stacks 338=HighIncidenceProgram.descendingHighMask H :=
    (hbf 338 (by decide)).trans hmask
  have hremaining : (b.stacks 863).length+(m.val 42)*((m.val 34)*baseWidth 3 (m.val 33))≤F := by
    rw [h863]
    exact hout
  obtain ⟨steps,z,codes,he,hlen,hvalue,happend,h301',h307',hguard,hpeek,hscratch,
      hfinalFrame,hfinal,hcost,_ht,hs⟩ :=
    nodeSource_run query k hg first tail node a bits remaining A hbank hparked ra rd rc words hc
      m ht hd M cache half e ho.produced hfield hv hJ source hsource high F
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A) (QueryHeadBudgets.transient A)
      A (resources).headSize caps cap hheads b np hp ha hb common hzero hmast hbf
      hcurrentMask haddress h832 h833 h834 h835 h301 hremaining hnext
  have pairCost := StreamedQueryMeasuredCost.addressed_pair_cost query k RB RC RD RI RE hg
    first tail node physical ready A bounded ra rd rc words hc m padding hm ht hd M cache half e
    ho.produced hfield hv hJ source hsource A (Nat.le_refl A) hvalues
  have pairSpace := StreamedQueryMeasuredCost.addressed_pair_space query k hg first tail node
    physical ready A bounded ra rd rc words hc m ht hd M cache half e ho.produced hfield hv hJ
    source hsource A (Nat.le_refl A) hvalues
  change DifferencePairsProgram.cost
    (QueryPairEvaluation.callbackBudget src factor ((native).n-(H).card) F
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
      (QueryHeadBudgets.transient A) (resources).headSize)
    ((native).n-(H).card) factor.J ≤
      StreamedQueryMeasuredCost.pairCoefficient A*work^2+10 at pairCost
  refine ⟨words,hc,steps,z,codes,he,hlen,hvalue,happend,h301',h307',hguard,hpeek,hscratch,
    hfinalFrame,hfinal,?_,?_⟩
  · change steps≤prepareBudget A+StreamedQueryMeasuredCost.pairCoefficient A*work^2+10+
      finishBudget (native).n (m.val 33) (m.val 34) (m.val 42) A
    change np≤prepareBudget A at hpt
    change steps≤np+DifferencePairsProgram.cost
      (QueryPairEvaluation.callbackBudget src factor ((native).n-(H).card) F
        (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
        (QueryHeadBudgets.transient A) (resources).headSize)
      ((native).n-(H).card) factor.J+
      finishBudget (native).n (m.val 33) (m.val 34) (m.val 42) A at hcost
    omega
  · apply hs.mono
    exact max_le_max pairSpace (by
      change 896*F+np+finishBudget (native).n (m.val 33) (m.val 34) (m.val 42) A+1≤_
      change np≤prepareBudget A at hpt
      omega)


omit hm hQ hR in
/-- The actual initialized node loop retains each emitted coefficient word
and the cache witness from that same execution. A reference target is chosen
only after the nonempty, ordered output stream has been produced. -/
theorem nodes_run (high : H → Bool) (A : ℕ) (a : State 40 896)
    (frontBase front : State 40 768) (bw : Bank.Words)
    (hf : Query.FrontState query k frontBase front padding bw)
    (hpark : ∀ j : Fin 14,
      a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j)) =
        (PackingCallerProgram.result front (Query.packingProblem query k hg)
          first tail).stacks (LayoutMasters.high j))
    (hparked : ∀ j : Fin 14,
      (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length≤A)
    (hcache : ∀ i∈cacheInputPorts,(a.stacks i).length≤A)
    (hvalues : ∀ i,m.val i≤A)
    (hsources : Query.Sources query (projectState (id : Fin 40 → Fin 40) QueryAssembler.Nodes.lowPort a))
    (h700 : (a.stacks 700).length≤A) (h701 : (a.stacks 701).length≤A)
    (h708 : (a.stacks 708).length≤A)
    (hnodes : a.stacks 300=Encoding.encodeList id
      (RingNodeMetadata.nodeBits (m.val 33) (m.val 34) (m.val 21)))
    (hmask : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (hframe : ∀ i∈QueryReadyConstruction.arithmeticPorts,a.stacks (i.castAdd 128)=out.stacks i)
    (hdegree : out.stacks 204=List.replicate (m.val 34) true)
    (h704 : a.stacks 704=List.replicate query.rows.length true)
    (h705 : a.stacks 705=Encoding.encodeNat (markIndex query))
    (h706 : a.stacks 706=[query.mark.isSome])
    (h702 : a.stacks 702=List.ofFn
      (fun v : Fin (BinaryArithmetic.toNat query.ambient) => decide (v ∈ H)))
    (h703 : a.stacks 703=List.ofFn
      (fun v : Fin (BinaryArithmetic.toNat query.ambient) =>
        if h : v ∈ H then high ⟨v, h⟩ else false))
    (ha : WordBound (QueryHeadBudgets.compact A) a)
    (model_eq : m = Execute.guardedModel (query.input k) padding)
    (query_count : m.val 21 = (native).Q)
    (radius_eq : (base.stacks 740).length = (native).R) :
    ∃ words, ∃ hc : CacheCorrect (native).height (unary (native).R) (native).width words,
    ∃ (steps : ℕ) (z : Data) (outputs : List (List Bool)),
      let factor := nativeSpecOfInputs native m ht hd words hc M cache half e ho.produced
        hfield query hv (m.val 42) hJ source hsource
      Eval QueryStreamProgram.nodes steps a z ∧
      NodeBoundary a (m.val 33) (m.val 34) (m.val 21) (m.val 42)
        (QueryHeadBudgets.compact A) (m.val 21) z ∧
      outputs.length=m.val 21 ∧ z.stacks 863=outputs.flatten ∧
      (∀ i (hi : i<outputs.length),
        ∃ codes : List (DensePolynomialProgram.Coeff (baseWidth 3 (m.val 33)) (m.val 34)),
          codes.length=m.val 42 ∧
          codes.map factor.p.ops.decode=List.ofFn
            (Truncated.ofPolynomial (m.val 42) ((NodeConcrete.specTarget factor H high).comp
              (Polynomial.X+Polynomial.C (factor.p.ops.decode
                (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i+1)))))).coeff ∧
          outputs[i]'hi=(codes.map RingProgram.flat).flatten) ∧
      steps≤23*QueryHeadBudgets.compact A+
        (m.val 21)*(nodeBudget (native).n (m.val 33) (m.val 34) (m.val 42) A work+1)+32 ∧
      QueryExecution.PrefixBound QueryStreamProgram.nodes (steps+1) a
        (max (919*QueryHeadBudgets.compact A+31)
          (nodeSpace (native).n (m.val 33) (m.val 34) (m.val 42) A)) := by
  let F := QueryHeadBudgets.compact A
  let ns := RingNodeMetadata.nodeBits (m.val 33) (m.val 34) (m.val 21)
  let I := NodeBoundary a (m.val 33) (m.val 34) (m.val 21) (m.val 42) F
  let P := fun i bytes =>
    ∃ words, ∃ hc : CacheCorrect (native).height (unary (native).R) (native).width words,
    ∃ codes : List (DensePolynomialProgram.Coeff (baseWidth 3 (m.val 33)) (m.val 34)),
      let factor := nativeSpecOfInputs native m ht hd words hc M cache half e ho.produced
        hfield query hv (m.val 42) hJ source hsource
      codes.length=m.val 42 ∧
      codes.map factor.p.ops.decode=List.ofFn
        (Truncated.ofPolynomial (m.val 42) ((NodeConcrete.specTarget factor H high).comp
          (Polynomial.X+Polynomial.C (factor.p.ops.decode
            (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i+1)))))).coeff ∧
      bytes=(codes.map RingProgram.flat).flatten
  have physical : ∀ i b,I i b → b.stacks 301=Encoding.encodeList id (ns.drop i) ∧
      b.stacks 307=List.replicate i true ∧ b.regs 37= !(ns.drop i).isEmpty ∧ WordBound F b := by
    intro i b hb
    exact ⟨hb.cursor,hb.node,hb.guard,hb.bounded⟩
  have capacity := QueryNodeSourceBounds.model_capacity m A hvalues
  have step : ∀ i b, i < ns.length → I i b →
      ∃ steps c bytes, steps ≤ nodeBudget (native).n (m.val 33) (m.val 34) (m.val 42) A work ∧
        Eval QueryStreamProgram.nodeBody steps b c ∧ I (i + 1) c ∧ P i bytes ∧
        c.stacks 863 = b.stacks 863 ++ bytes ∧
        ∀ p q, p ≤ steps → Trace (compiled QueryStreamProgram.nodeBody 0 0) p
          (b.withPC (some (compiled QueryStreamProgram.nodeBody 0 0).entry)) q →
          ∀ port,(q.stacks port).length≤nodeSpace (native).n (m.val 33) (m.val 34) (m.val 42) A := by
    intro i b hi hb
    have him : i < m.val 21 := by
      simpa only [ns, RingNodeMetadata.nodeBits_length] using hi
    let ix : Fin (Query.packingProblem query k hg).Q := ⟨i,by
      change i < (native).Q
      omega⟩
    have bank := hb.sourceBank query k hg frontBase front padding bw hf first tail ix hpark
    obtain ⟨cacheCap,parkCap⟩ := hb.input_caps hcache hparked
    have sources : Query.Sources query
        (projectState (id : Fin 40 → Fin 40) QueryAssembler.Nodes.lowPort b) := by
      exact ⟨(hb.retained 700 (by decide)).trans hsources.formula,
        (hb.retained 701 (by decide)).trans hsources.rows,
        (hb.retained 707 (by decide)).trans hsources.modulus,
        (hb.retained 708 (by decide)).trans hsources.width,
        (hb.retained 709 (by decide)).trans hsources.ambient⟩
    have cursor : b.stacks 301=Encoding.encodeList id
        (RingProgram.flat (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (ix.val+1))::ns.drop (i+1)) := by
      rw [hb.cursor,RingNodeMetadata.nodeBits_drop _ _ _ ⟨i,him⟩]
    have room := hb.room him capacity.2 capacity.1
    obtain ⟨words,hc,steps,c,codes,he,hlen,hvalue,happend,h301,h307,hguard,_hpeek,hscratch,
        hfinalFrame,hbound,hcost,hspace⟩ :=
      node_run query k RB RC RD RI RE hg hv first tail ix m padding model_eq ht hd M cache half e
        base out ho hfield query_count radius_eq hJ source hsource high A b (ns.drop (i+1))
        bank parkCap cacheCap
        hvalues sources (by rw [hb.retained 700 (by decide)]; exact h700)
        (by rw [hb.retained 701 (by decide)]; exact h701)
        (by rw [hb.retained 708 (by decide)]; exact h708) cursor
        ((hb.retained 338 (by decide)).trans hmask) (hb.arithmetic out hframe) hdegree
        ((hb.retained 704 (by decide)).trans h704)
        ((hb.retained 705 (by decide)).trans h705)
        ((hb.retained 706 (by decide)).trans h706)
        ((hb.retained 702 (by decide)).trans h702)
        ((hb.retained 703 (by decide)).trans h703) hb.bounded room.1
    refine ⟨steps,c,(codes.map RingProgram.flat).flatten,hcost,he,?_,?_,happend,?_⟩
    · exact hb.next codes hlen h301 h307 hguard (fun j hj =>
        hfinalFrame j (List.mem_filter.mp hj).1
          (of_decide_eq_true (List.mem_filter.mp hj).2).1
          (of_decide_eq_true (List.mem_filter.mp hj).2).2) happend hscratch hbound
    · exact ⟨words,hc,codes,hlen,hvalue,rfl⟩
    · intro p q hp hq port
      exact hspace.bound p q (by omega) hq port
  obtain ⟨steps,z,outputs,hcost,he,hend,hlen,houtputs,_hcursor,_hindex,_hguard,hstream,hbound,hprefix⟩ :=
    QueryNodeLoopSpace.nodes_eval_prefix ns I P F
      (nodeSpace (native).n (m.val 33) (m.val 34) (m.val 42) A)
      (nodeBudget (native).n (m.val 33) (m.val 34) (m.val 42) A work)
      physical step a ha (initialized_boundary a _ _ _ _ F hnodes ha)
  have hlen' : outputs.length=m.val 21 := by simpa only [ns,RingNodeMetadata.nodeBits_length] using hlen
  have hpositive : 0 < m.val 21 := by
    have hp := node.isLt
    change node.val < (native).Q at hp
    omega
  obtain ⟨words,hc,_codes,_hlen,_value,_bytes⟩ := houtputs 0 (by omega)
  refine ⟨words,hc,steps,z,outputs,he,?_,hlen',hstream,?_,?_,⟨?_⟩⟩
  · simpa only [ns,RingNodeMetadata.nodeBits_length] using hend
  · intro i hi
    obtain ⟨words',hc',codes,hlen,hvalue,hbytes⟩ := houtputs i hi
    exact ⟨codes,hlen,hvalue,hbytes⟩
  · simpa only [ns,RingNodeMetadata.nodeBits_length] using hcost
  · exact StructuredSpace.compiled_halt_stack_bound he 838 838 hprefix


include hm hQ hR in
/-- The fixed conditioned query executes high decoding, all interpolation
nodes, and canonical reconstruction on one trace. The count is obtained from
the actual source target and the same emitted coefficient bytes. -/
theorem run (A S : ℕ) (a : State 40 896)
    (frontBase front : State 40 768) (bw : Bank.Words)
    (hf : Query.FrontState query k frontBase front padding bw)
    (hpark : ∀ j : Fin 14,
      a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j)) =
        (PackingCallerProgram.result front (Query.packingProblem query k hg)
          first tail).stacks (LayoutMasters.high j))
    (hparked : ∀ j : Fin 14,
      (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length≤A)
    (hcache : ∀ i∈cacheInputPorts,(a.stacks i).length≤A)
    (hvalues : ∀ i,m.val i≤A)
    (hsources : Query.Sources query (projectState (id : Fin 40 → Fin 40) QueryAssembler.Nodes.lowPort a))
    (h700 : (a.stacks 700).length≤A) (h701 : (a.stacks 701).length≤A)
    (h708 : (a.stacks 708).length≤A)
    (hnodes : a.stacks 300=Encoding.encodeList id
      (RingNodeMetadata.nodeBits (m.val 33) (m.val 34) (m.val 21)))
    (hmask : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (hframe : ∀ i∈QueryReadyConstruction.arithmeticPorts,a.stacks (i.castAdd 128)=out.stacks i)
    (hdegree : out.stacks 204=List.replicate (m.val 34) true)
    (h704 : a.stacks 704=List.replicate query.rows.length true)
    (h705 : a.stacks 705=Encoding.encodeNat (markIndex query))
    (h706 : a.stacks 706=[query.mark.isSome])
    (counterWords : List (List Bool))
    (hshape : counterWords.map List.length=List.replicate (H).card 1)
    (rank : Fin (2^(H).card)) (hrank : CounterPrograms.value counterWords.flatten=rank.val)
    (hcounter : a.stacks 330=Encoding.encodeList id counterWords)
    (hring : ∀ i∈QueryReconstruction.ringPorts,
      a.stacks (i.castAdd 576)=e.stacks (i.castAdd 320))
    (hflat : a.stacks 256=e.stacks 256)
    (hwidth : ∀ clause∈source,clause.length≤k)
    (ha : WordBound (QueryHeadBudgets.compact A) a)
    (hAS : A≤S) (hqsize : 3^(m.val 34)≤S)
    (hmodsize : (a.stacks 194).length≤S) (hwidthsize : (a.stacks 202).length≤S)
    (hambient : (native).n+1≤QueryHeadBudgets.compact A) :
    ∃ words, ∃ hc : CacheCorrect (native).height (unary (native).R) (native).width words,
    ∃ steps final,
      let high := HighIncidenceProgram.Rank.highEquiv (HighIncidenceProgram.Order.highOrder H) rank
      let factor := nativeSpecOfInputs native m ht hd words hc M cache half e ho.produced
        hfield query hv (m.val 42) hJ source hsource
      Eval QueryStreamProgram.command steps a final ∧
      Trace QueryStreamProgram.program (steps+1)
        (a.withPC (some QueryStreamProgram.program.entry)) (final.withPC none) ∧
      final.stacks 323=DisjointReuse.binaryNat
        (NodeSemantics.ternaryFixedHighCount H high (NodeConcrete.sourceHashes factor)
          factor.marked factor.markedClause) ∧
      final.stacks 863=[] ∧ WordBound (QueryHeadBudgets.compact A) final ∧
      (∀ i∈retainedPorts,i≠702 → i≠703 → final.stacks i=a.stacks i) ∧
      (∀ i,HashMarkedReturn.kept i=true → final.stacks i=a.stacks i) ∧
      steps+1≤budget (native).n (m.val 33) (m.val 34) (m.val 21) (m.val 42) A S work ∧
      QueryExecution.PrefixBound QueryStreamProgram.command (steps+1) a
        (space (native).n (m.val 33) (m.val 34) (m.val 42) A S) := by
  let F := QueryHeadBudgets.compact A
  let high := HighIncidenceProgram.Rank.highEquiv (HighIncidenceProgram.Order.highOrder H) rank
  obtain ⟨np,rf,hp,hpt,h702,h703,hpf,hb,hps⟩ :=
    HighQueryLoop.prepare_high_resources H counterWords hshape rank hrank a F F
      hcounter hmask (ha 330) (ha 338) (fun i _ => ha i) ha
  let b := HighQueryAdapter.highResult (HighQueryAdapter.resetHighState a) rf counterWords.flatten
  have bp : ∀ j : Fin 14,b.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))=
      a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j)) := by
    intro j
    apply hpf
    fin_cases j <;> decide
  have bc : ∀ i∈cacheInputPorts,b.stacks i=a.stacks i := by
    intro i hi
    apply hpf
    simp only [cacheInputPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have bf : ∀ i∈QueryReadyConstruction.arithmeticPorts,b.stacks (i.castAdd 128)=out.stacks i := by
    intro i hi
    apply Eq.trans (hpf _ ?_) (hframe i hi)
    simp only [QueryReadyConstruction.arithmeticPorts, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have bs : Query.Sources query
      (projectState (id : Fin 40 → Fin 40) QueryAssembler.Nodes.lowPort b) :=
    ⟨(hpf 700 (by decide)).trans hsources.formula,
      (hpf 701 (by decide)).trans hsources.rows,
      (hpf 707 (by decide)).trans hsources.modulus,
      (hpf 708 (by decide)).trans hsources.width,
      (hpf 709 (by decide)).trans hsources.ambient⟩
  obtain ⟨words,hc,nn,c,outputs,he,hi,hlen,hstream,houtputs,hnt,hns⟩ :=
    nodes_run query k RB RC RD RI RE hg hv first tail node m padding ht hd M cache half e
      base out ho hfield hJ source hsource high A b frontBase front bw hf
      (fun j => (bp j).trans (hpark j)) (fun j => by rw [bp j]; exact hparked j)
      (fun i h => by rw [bc i h]; exact hcache i h) hvalues bs
      (by rw [hpf 700 (by decide)]; exact h700)
      (by rw [hpf 701 (by decide)]; exact h701)
      (by rw [hpf 708 (by decide)]; exact h708)
      ((hpf 300 (by decide)).trans hnodes) ((hpf 338 (by decide)).trans hmask) bf hdegree
      ((hpf 704 (by decide)).trans h704) ((hpf 705 (by decide)).trans h705)
      ((hpf 706 (by decide)).trans h706) h702 h703 hb hm hQ hR
  have hpositive : 0 < m.val 21 := by
    have hn := node.isLt
    change node.val < (native).Q at hn
    omega
  have cring : ∀ i∈QueryReconstruction.ringPorts,
      c.stacks (i.castAdd 576)=e.stacks (i.castAdd 320) := by
    intro i hii
    have hm : i.castAdd 576∈retainedPorts := by
      simp only [QueryReconstruction.ringPorts, List.mem_cons,
        List.not_mem_nil, or_false] at hii
      rcases hii with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have hd : i.castAdd 576∉HighQueryAdapter.highChanged := by
      simp only [QueryReconstruction.ringPorts, List.mem_cons,
        List.not_mem_nil, or_false] at hii
      rcases hii with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    exact (hi.retained _ hm).trans ((hpf _ hd).trans (hring i hii))
  obtain ⟨nr,final,hrt,hr,htrace,hcount,hblank,hfinal,hu,h320,h322,hlow,hret,_hreg,hrs⟩ :=
    QueryCountReconstruction.query_run_space_with_full_frame query k hg hv first tail node
      padding m hm ht hd words hc M cache half e ho.produced source hsource H high hwidth
      c (hi.readout_scratch hpositive) cring
      ((hi.retained 256 (by decide)).trans ((hpf 256 (by decide)).trans hflat)) outputs hlen hstream
      (fun i => houtputs i.val (by omega)) F S hi.bounded
      ((hvalues 21).trans hAS) ((hvalues 42).trans hAS) ((hvalues 33).trans hAS)
      ((hvalues 34).trans hAS) hqsize
      (by rw [hi.retained 194 (by decide),hpf 194 (by decide)]; exact hmodsize)
      (by rw [hi.retained 202 (by decide),hpf 202 (by decide)]; exact hwidthsize) hambient
  have rsp : QueryExecution.PrefixBound QueryReconstruction.command (nr+1) c
      (896*F+QueryReconstruction.budget F S) := ⟨hrs⟩
  have dsp : QueryExecution.PrefixBound HighQueryAdapter.prepareHigh (np+1) a
      (67*F+37) := ⟨fun p q hle ht i =>
    (hps.bound p q hle ht i).trans (max_le (Nat.le_refl _) (by omega))⟩
  obtain ⟨whole,trace,spaceBound⟩ := command_eval_prefix hp he hr dsp hns rsp
  have finalFrame : ∀ i∈retainedPorts,i≠702 → i≠703 → final.stacks i=a.stacks i := by
    intro i him h702i h703i
    have ht : final.stacks i=c.stacks i := by
      have cases : i∈QueryReconstruction.retainedPorts ∨ i=320 ∨ i=322 ∨
          ((330 : ℕ) ≤ i.val ∧ i.val < 768 ∧ i ≠ 699) := by
        have hm := (List.mem_filter.mp him).1
        simp only [framePorts, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals first | decide | simp [retainedPorts] at him
      rcases cases with hc|rfl|rfl|⟨hlo,hhi,hne⟩
      · exact hret i hc
      · exact h320
      · exact h322
      · exact hlow i hlo hhi hne
    have hd : i∉HighQueryAdapter.highChanged := by
      intro hh
      simp only [HighQueryAdapter.highChanged, List.mem_cons,
        List.not_mem_nil, or_false] at hh
      rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals first | exact h702i rfl | exact h703i rfl | simp [retainedPorts,framePorts] at him
    exact ht.trans ((hi.retained i him).trans (hpf i hd))
  refine ⟨words,hc,np+nn+nr,final,whole,trace,hcount,hblank,hfinal,finalFrame,?_,?_,?_⟩
  · apply QueryKeptFrame.kept_frame whole
    intro i hii
    apply finalFrame i ?_ ?_ ?_
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hii
      rcases hii with rfl|rfl|rfl|rfl|rfl <;> decide
  · change np≤18*F+65*(native).n+67 at hpt
    change np+nn+nr+1≤18*F+65*(native).n+67+23*F+
      (m.val 21)*(nodeBudget (native).n (m.val 33) (m.val 34) (m.val 42) A work+1)+32+
      QueryReconstruction.budget F S
    omega
  · exact spaceBound

end ActualNode

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect

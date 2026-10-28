import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryWordBounds

/-! Concrete capacities for the actual addressed node source. Its reference
snapshot is bounded only by retained query words, independently of caller
scratch, node index and the actual bootstrap cache witness. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds
open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram LeafParametersProgram LeafProgram
open QueryNodeEvaluation

/-- Ordinary cache and output arrays fit the same already fixed compact
cap; this bound contains no callback count or transient budget. -/
theorem compact_capacity (A : ℕ) : 20*(A+1)^4 ≤ QueryHeadBudgets.compact A := by
  have hp : (A+1)^4 ≤ (A+2)^6 :=
    (Nat.pow_le_pow_left (by omega : A+1≤A+2) 4).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  apply le_trans (b := SignatureTupleComplete.retainedEnvelope A 0) ?_
    (TupleRunBudgets.retained_le_compact A A (Nat.le_refl A))
  have hm : 20*(A+1)^4 ≤ 10000*(A+2)^6 := Nat.mul_le_mul (by decide) hp
  unfold SignatureTupleComplete.retainedEnvelope
  omega

/-- The full ordered output array fits before any node cache is produced. -/
theorem array_capacity (Q J d t A : ℕ)
    (hQ : Q≤A) (hJ : J≤A) (hd : d≤A) (ht : t≤A) :
    Q*(J*(d*SubexpLiftRing.baseWidth 3 t))≤QueryHeadBudgets.compact A ∧
    Q≤QueryHeadBudgets.compact A := by
  have hword : Q*(J*(d*SubexpLiftRing.baseWidth 3 t))≤A*(A*(A*(2*A))) := by
    simp only [RingProgram.ternary_baseWidth]
    gcongr
  have hp : 2*A^4≤20*(A+1)^4 := Nat.mul_le_mul (by decide)
    (Nat.pow_le_pow_left (by omega) 4)
  have hA : A≤QueryHeadBudgets.compact A := by
    have h := QueryHeadBudgets.original_le_scalar A
    have hh := HeadSumBudgets.compact_le (QueryHeadBudgets.scalarCap A)
    change _ ≤ QueryHeadBudgets.compact A at hh
    omega
  refine ⟨?_,hQ.trans hA⟩
  apply hword.trans
  calc
    A*(A*(A*(2*A))) = 2*A^4 := by ring
    _ ≤ 20*(A+1)^4 := hp
    _ ≤ QueryHeadBudgets.compact A := compact_capacity A

/-- The authentic scalar bank supplies capacity before entering the node
loop; this theorem has no later cache or source witness argument. -/
theorem model_capacity (m : Circuit.Model) (A : ℕ) (hvalues : ∀ i,m.val i≤A) :
    (m.val 21)*((m.val 42)*((m.val 34)*SubexpLiftRing.baseWidth 3 (m.val 33)))≤
      QueryHeadBudgets.compact A ∧
    m.val 21≤QueryHeadBudgets.compact A :=
  array_capacity _ _ _ _ A (hvalues 21) (hvalues 42) (hvalues 34) (hvalues 33)

/-- The paid native bootstrap's actual retained cache words fit the same
compact node boundary, independently of the chosen cache encoding witness. -/
theorem bootstrap_capacity_of_ready (s : Native.Inputs)
    (state : LeafHeadSetupProgram.Data) (A : ℕ)
    (ready : Native.Ready s state) (bounded : WordBound A state) :
    SignatureHeadLoader.bootstrapOutputBound s ≤ QueryHeadBudgets.compact A := by
  have hi := NodeTime.inputBounds s state ready A bounded
  have hm := Nat.mul_le_mul hi.R hi.width
  have hp1 : A+1 ≤ (A+1)^4 := Nat.le_self_pow (by decide) _
  have hp2 : A^2 ≤ (A+1)^4 :=
    (Nat.pow_le_pow_left (by omega : A≤A+1) 2).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  have hcap : SignatureHeadLoader.bootstrapOutputBound s ≤ 20*(A+1)^4 := by
    unfold SignatureHeadLoader.bootstrapOutputBound
    have hQr := hi.Qr
    have hr := hi.r
    have hD := hi.D
    have hw := hi.width
    have hh := hi.height
    have hR := hi.R
    rw [pow_two] at hp2
    omega
  exact hcap.trans (compact_capacity A)


variable (query : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (query.input k))
  (first : MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q)
  (tail : List (MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem query k hg).Q)
local notation "native" => Native.queryInputsAddressed query k hg first tail node
variable (a : QueryNodeEvaluation.Data) (bits : List Bool) (remaining : List (List Bool)) (A : ℕ)
  (hbank : NativeLayoutLoad.SourceBank (Native.queryInputsAddressed query k hg first tail node) a)
  (hparked : ∀ j : Fin 14,
    (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length≤A)
  (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
  (hc : CacheCorrect (Native.queryInputsAddressed query k hg first tail node).height
    (unary (Native.queryInputsAddressed query k hg first tail node).R)
    (Native.queryInputsAddressed query k hg first tail node).width words)


local notation "src" => nodeSource query k hg first tail node a bits remaining A hbank hparked ra rd rc words hc
local notation "problem" => LeafProgram.Query.packingProblem query k hg

/-- The actual restricted source supplies the SAME compact cursor/frame/key
cap on every node, without using its prior transient scratch. -/
theorem retainedCap : SignatureTupleComplete.RetainedCap src (QueryHeadBudgets.compact A) :=
  TupleRunBudgets.retainedCap src A (Nat.le_refl A)

/-- Every emitted head cursor is bounded by the genuine selected-head
maximum from the original resource record, not by ambient storage slack. -/
theorem headSize_le (depth : ℕ) (hd : depth<(src).input.r) :
    (src).headSize depth ≤ LayoutProducedHeads.maxSelected (problem).n (problem).Q (problem).r
      (ProducedQueryRank.rows problem first tail) (query.forward.map Bool.not) := by
  exact SignatureTupleSourceAlignment.selected_length_le_max query k hg first tail node ⟨depth,hd⟩

/-- The guard actually executed by the query supplies the row-radius bound. -/
theorem radius : (src).input.R+1 ≤ (src).input.Q := by
  change (produce (query.input k)).R+1 ≤ (produce (query.input k)).Q
  have hQ := hg.2.2.2.2.2.2.1
  have hR := hg.2.2.2.2.2.2.2.1
  omega

/-- Specialization to the actual restricted addressed source. -/
theorem bootstrap_capacity :
    SignatureHeadLoader.bootstrapOutputBound (src).input ≤ QueryHeadBudgets.compact A :=
  bootstrap_capacity_of_ready (src).input (src).source A (src).ready (src).bounded

section Factor
variable (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : (Native.queryInputsAddressed query k hg first tail node).Q < 3^(m.val 34))
    (hv : query.Valid) (hJ : 0 < m.val 42)
    (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed query k hg first tail node).n))))
    (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source)
local notation "spec" => QueryReadyConstruction.sourceSpec src m ht hd M cache half e hp
  hfield query hv hJ source hsource

/-- The actual frontend words and actual produced scalar bank discharge
all one-head numeric fields for this SAME restricted node source. Width A
bounds literal storage only; the traversal still uses the selected-head size. -/
theorem headBounds
    (hvalues : ∀ i, m.val i ≤ A)
    (hsources : LeafProgram.Query.Sources query
      (projectState (id : Fin 40 → Fin 40) QueryAssembler.Nodes.lowPort a))
    (h700 : (a.stacks 700).length ≤ A)
    (h701 : (a.stacks 701).length ≤ A)
    (h708 : (a.stacks 708).length ≤ A) :
    QueryVisitorHead.HeadBounds (src).input spec A (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
      (QueryHeadBudgets.transient A) (src).bound A := by
  obtain ⟨hbit,hrows,hmark,hwidth⟩ := NativeQueryWordBounds.produced_words
    (src).input m ht hd (src).cacheWords (src).cache M cache half e hp
    hfield query hv (m.val 42) hJ source hsource
    (projectState (id : Fin 40 → Fin 40) QueryAssembler.Nodes.lowPort a) A
    hsources h700 h701 h708
  exact QueryHeadBudgets.headBounds (src).input spec (src).source A (src).bound A A
    (src).ready (src).bounded (Nat.le_refl A) (Nat.le_refl A)
    (hvalues 34) (hvalues 33) (hvalues 33) (hvalues 42) hbit (Nat.le_refl A)
    hrows hmark rfl rfl rfl (src).input.plans_length
    (radius query k hg first tail node a bits remaining A hbank hparked ra rd rc words hc) hwidth

/-- The complete ordered node-output prefix is paid for as an actual array,
not by a traversal-time bound. Q and every jet/coefficient dimension are fixed
by the same source and produced scalar bank. -/
theorem node_capacity (hvalues : ∀ i, m.val i ≤ A) :
    (src).input.Q*((spec).J*((m.val 34)*SubexpLiftRing.baseWidth 3 (spec).p.t)) ≤
        QueryHeadBudgets.compact A ∧
    (src).input.Q ≤ QueryHeadBudgets.compact A := by
  have hi := NodeTime.inputBounds (src).input (src).source (src).ready A (src).bounded
  exact array_capacity _ _ _ _ A hi.Q (hvalues 42) (hvalues 34) (hvalues 33)

/-- Actual measured tuple time and space are uniform in this node's index
and cache witness. The selected-head maximum remains the external exponent. -/
theorem run_bounds (hvalues : ∀ i, m.val i ≤ A) :
    SignatureTupleRun.completeSpace src spec (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.transient A) ≤ TupleRunBudgets.runCoefficient A ∧
    ∀ height, SignatureTupleRun.runTime src spec (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
      (QueryHeadBudgets.transient A) height ≤
      TupleRunBudgets.runCoefficient A*((src).input.r+1)*
        SignatureTupleRun.tupleCount (src).key (src).input.r*4^height :=
  TupleRunBudgets.run_bounds src spec A (Nat.le_refl A)
    (hvalues 34) (hvalues 33) (hvalues 33) (hvalues 42) rfl rfl rfl

end Factor

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds

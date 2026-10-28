import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeadsQuery
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgramSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsSemanticsEnumeration
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgramSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeAddressedQuery
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeMetadata
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendMask
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeySource
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyPackingTransport
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal

/-! The frontend's actual mask, the produced head rows and the authentic
source factory use the same ambient variables and the same full integer keys.
No selected-coordinate or factory-alignment witness is supplied by the caller. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSourceAlignment

open scoped BigOperators
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open MulticolorTypes Subexp.ConstructivePacking
open LeafHeadSetupProgram LeafParametersProgram LayoutProgram
open BucketTupleProgram.Concrete

/-- Reversing the physical descending mask gives the forward ambient mask. -/
theorem forward_bits (q : LeafQueryFrontend.Query) :
    q.forward = List.ofFn (fun v => decide (v ∈ HighMarkedFrontend.highSet q)) := by
  rw [LeafQueryFrontend.Query.forward, HighMarkedFrontend.physical_high_mask,
    HighIncidenceProgram.descendingHighMask,
    OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates_stream, List.reverse_reverse]

/-- Every ambient coordinate is retained, including variables with no source
occurrence. The low mask is the actual complement of the produced high set. -/
theorem low_bits (q : LeafQueryFrontend.Query) :
    q.forward.map Bool.not =
      HeadIdentifierProgram.lowBits (fun v => decide (v ∉ HighMarkedFrontend.highSet q)) := by
  rw [forward_bits]
  simp [HeadIdentifierProgram.lowBits, List.map_ofFn, Function.comp_def]

/-- Equality of all raw rows is unchanged by the actual length cast. -/
theorem row_cast_eq_iff {D E : ℕ} (h : D = E) (f g : Fin E → ℤ) :
    (fun j : Fin D => f (Fin.cast h j)) = (fun j => g (Fin.cast h j)) ↔ f = g := by
  cases h
  rfl

section Query
attribute [local instance] Classical.propDecidable
variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
local notation "p" => LeafProgram.Query.packingProblem q k hg
variable (first : Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q)
  (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem q k hg).Q)
local notation "s" => Native.queryInputsAddressed q k hg first tail node
local notation "H" => HighMarkedFrontend.highSet q
local notation "head" => (fun t v => ProducedQueryRank.words p first tail (Sum.inl v) t)
local notation "owner" => ProducedQueryRank.owner p
local notation "js" => (fun g : Fin (PackingCallerProgram.Problem.r p) =>
  selectedHeads (Native.Inputs.n s) (Native.Inputs.rows s) (Native.Inputs.low s)
    (Fin.val node * PackingCallerProgram.Problem.r p + Fin.val g))
include q k hg first tail node

theorem query_low_bits :
    (s).low = HeadIdentifierProgram.lowBits (fun v => decide (v ∉ H)) := low_bits q

theorem query_rows_length : (s).rows.length = (s).n+(s).N := by
  change (ProducedQueryRank.rows p first tail).length = (p).n+(p).factors
  simp [ProducedQueryRank.rows, PackingCallerProgram.Problem.words_length]

/-- Factor rows follow all ambient head rows in the actual produced table. -/
theorem factor_row (f : Fin (p).factors) :
    (s).rows.getD ((p).n+f.val) [] =
      Subexp.ReadPlan.encodeWord (ProducedQueryRank.words p first tail (.inr f)) := by
  have hf : (p).n+f.val < ((p).words first tail).length := by
    rw [(p).words_length]
    omega
  change (((p).words first tail).map Subexp.ReadPlan.encodeWord).getD ((p).n+f.val) [] = _
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hf), List.getElem_map]
  rfl

theorem factor_predicate (g : Fin (p).r) (f : Fin (p).factors) :
    LeafHeadFactorsProgram.predicate (s).rows (s).n (node.val*(p).r+g.val) f.val =
      decide (ProducedQueryRank.words p first tail (.inr f) node = g) := by
  change ((s).rows.getD ((p).n+f.val) []).getD (node.val*(p).r+g.val) false = _
  rw [factor_row, HeadIdentifierProgram.encodeWord_getD]

theorem factor_selected_mem (g : Fin (p).r) (f : Fin (p).factors) :
    f.val ∈ LeafHeadFactorsProgram.chosenIds
      (LeafHeadFactorsProgram.predicate (s).rows (s).n (node.val*(p).r+g.val)) (s).N ↔
      ProducedQueryRank.words p first tail (.inr f) node = g := by
  simp only [LeafHeadFactorsProgram.chosenIds, List.mem_filter, List.mem_range]
  change (f.val < (p).factors ∧
    LeafHeadFactorsProgram.predicate (s).rows (s).n (node.val*(p).r+g.val) f.val=true) ↔ _
  rw [factor_predicate q k hg first tail node g f]
  simp only [f.isLt, true_and, decide_eq_true_eq]

/-- The physical factor stream is the complete increasing filter by its
produced color, including every neutral factor for an unused low variable. -/
theorem factor_ids (g : Fin (p).r) :
    LeafHeadFactorsProgram.chosenIds
      (LeafHeadFactorsProgram.predicate (s).rows (s).n (node.val*(p).r+g.val)) (s).N =
      (List.range (p).factors).filter (fun f =>
        if hf : f < (p).factors then
          decide (ProducedQueryRank.words p first tail (.inr ⟨f,hf⟩) node = g)
        else false) := by
  apply List.filter_congr
  intro f hf
  have hlt : f < (p).factors := List.mem_range.mp hf
  simpa only [dite_eq_left hlt] using
    factor_predicate q k hg first tail node g ⟨f,hlt⟩

theorem factor_selected_nodup (g : Fin (p).r) :
    (LeafHeadFactorsProgram.chosenIds
      (LeafHeadFactorsProgram.predicate (s).rows (s).n (node.val*(p).r+g.val)) (s).N).Nodup :=
  LeafHeadFactorsProgram.chosenIds_nodup _ _

/-- Every produced factor occurs in exactly one group. This quantifies over
all factor IDs, so a neutral factor cannot be omitted by head incidence tests. -/
theorem factor_partition (f : Fin (p).factors) :
    ∃! g : Fin (p).r, f.val ∈ LeafHeadFactorsProgram.chosenIds
      (LeafHeadFactorsProgram.predicate (s).rows (s).n (node.val*(p).r+g.val)) (s).N := by
  refine ⟨ProducedQueryRank.words p first tail (.inr f) node, ?_, ?_⟩
  · exact (factor_selected_mem q k hg first tail node _ f).2 rfl
  · intro g hmem
    exact ((factor_selected_mem q k hg first tail node g f).1 hmem).symm

/-- The actual row lookup selects exactly the free coordinates of the
produced head, without a packing-coverage or occurrence premise. -/
theorem selected_mem (g : Fin (p).r) (v : Fin (p).n) :
    v.val ∈ js g ↔ v ∉ H ∧ head node v = g := by
  change v.val ∈ selectedHeads (p).n (ProducedQueryRank.rows p first tail)
    (q.forward.map Bool.not) (node.val*(p).r+g.val) ↔ _
  rw [low_bits q]
  simp only [selectedHeads, HeadIdentifierProgram.chosenIds, List.mem_filter,
    List.mem_range, v.isLt, true_and, HeadIdentifierProgram.predicate]
  rw [ProducedQueryRank.head_row, HeadIdentifierProgram.encodeWord_getD]
  have hvl : v.val < BinaryArithmetic.toNat q.ambient := v.isLt
  let v' : Fin (BinaryArithmetic.toNat q.ambient) := ⟨v.val,hvl⟩
  have hv : v'=v := Fin.ext rfl
  have hl : (HeadIdentifierProgram.lowBits (fun w => decide (w ∉ H))).getD v.val false =
      decide (v' ∉ H) := by
    unfold HeadIdentifierProgram.lowBits
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hvl),
      List.getElem_ofFn]
  rw [hl]
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  rw [hv]
  exact Iff.rfl

theorem selected_mask (g : Fin (p).r) :
    List.ofFn (fun v : Fin (p).n =>
      HeadIdentifierProgram.predicate (s).rows (s).low (node.val*(p).r+g.val) v.val) =
      List.ofFn (fun v : Fin (p).n => decide (v ∉ H ∧ head node v=g)) := by
  apply congrArg List.ofFn
  funext v
  apply Bool.eq_iff_iff.mpr
  have hv : v.val < (s).n := v.isLt
  simpa only [selectedHeads, HeadIdentifierProgram.chosenIds, List.mem_filter,
    List.mem_range, hv, true_and, decide_eq_true_eq] using
    selected_mem q k hg first tail node g v

theorem selected_spec (g : Fin (p).r) (v : Fin (p).n) :
    v.val ∈ js g ↔ ∃ _ : v ∉ H, head node v = g :=
  by simpa only [exists_prop] using selected_mem q k hg first tail node g v

theorem selected_bound (g : Fin (p).r) : ∀ v ∈ js g, v < (p).n :=
  HeadIdentifierProgram.chosenIds_bound _ _

theorem selected_nodup (g : Fin (p).r) : (js g).Nodup :=
  HeadIdentifierProgram.chosenIds_nodup _ _

/-- The semantic free-head width is exactly the emitted cursor width. -/
theorem free_head_card (g : Fin (p).r) :
    Fintype.card (Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g) =
      (js g).length := by
  exact (Fintype.card_congr (freeOrder H (fun v => head node v.val) g (js g)
    (selected_bound q k hg first tail node g)
    (selected_nodup q k hg first tail node g)
    (selected_spec q k hg first tail node g)).symm).trans (Fintype.card_fin _)

/-- The runtime exponent uses the original actual maximum over selected
node/head widths. Ambient n bounds retained storage separately. -/
theorem selected_length_le_max (g : Fin (p).r) :
    (js g).length ≤ LayoutProducedHeads.maxSelected (p).n (p).Q (p).r
      (ProducedQueryRank.rows p first tail) (q.forward.map Bool.not) :=
  LayoutProducedHeads.selected_le_max _ _ _ _ _ node g

theorem free_head_card_le_max (g : Fin (p).r) :
    Fintype.card (Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g) ≤
      LayoutProducedHeads.maxSelected (p).n (p).Q (p).r
        (ProducedQueryRank.rows p first tail) (q.forward.map Bool.not) := by
  rw [free_head_card]
  exact selected_length_le_max q k hg first tail node g

omit node in
/-- The same actual maximum has the original balanced packing bound. The
alphabet premises are discharged by the physical complete-alphabet producer. -/
theorem maximum_width_budget (haN : (first::tail).Nodup) (haC : ∀ z,z∈first::tail) :
    (LayoutProducedHeads.maxSelected (p).n (p).Q (p).r
      (ProducedQueryRank.rows p first tail) (q.forward.map Bool.not) : ℝ) ≤
      2*(BinaryArithmetic.toNat q.ambient:ℝ)/Asymptotic.layoutR (q.input k).freeCount :=
  LayoutProducedHeads.query_max_bound_real q k hg first tail haN haC

theorem selected_width_budget (haN : (first::tail).Nodup) (haC : ∀ z,z∈first::tail)
    (g : Fin (p).r) :
    ((js g).length : ℝ) ≤
      2*(BinaryArithmetic.toNat q.ambient:ℝ)/Asymptotic.layoutR (q.input k).freeCount := by
  have hs : ((js g).length : ℝ) ≤
      (LayoutProducedHeads.maxSelected (p).n (p).Q (p).r
        (ProducedQueryRank.rows p first tail) (q.forward.map Bool.not) : ℝ) := by
    exact_mod_cast selected_length_le_max q k hg first tail node g
  exact hs.trans (maximum_width_budget q k hg first tail haN haC)

/-- The owner and head are read from the original produced packing. -/
theorem owner_head (i : Fin (s).D) (t : Fin (s).Q) :
    ((s).packing.label i).head t = head t (owner i) :=
  ProducedQueryRank.packing_head p first tail i t

omit first tail node in
/-- Every actual incidence owner is low; unused low coordinates still
participate in selected_mem independently of whether they own an incidence. -/
theorem owner_low (i : Fin (p).incidences) : owner i ∉ H := by
  let entry := (PackingIncidenceInput.Semantics.nativeEntries (p).scopes (p).mask).get i
  have hm := List.get_mem (PackingIncidenceInput.Semantics.nativeEntries (p).scopes (p).mask) i
  have hl := LeafStatisticsSemantics.entries_owner_low (p).scopes (p).mask 0 (p).scopes.length
    entry.1 entry.2 hm
  obtain ⟨j,hj,hb⟩ := (LeafStatisticsSemantics.lowOwners_mem 0 entry.1 (p).mask).mp hl
  have hj' : j.val = (owner i).val := by
    change j.val = entry.1
    simpa only [Nat.zero_add] using hj
  have hmask : q.forward.getD (owner i).val false = false := by
    change (p).mask.getD (owner i).val false = false
    rw [← hj', List.getD_eq_getElem _ _ j.isLt]
    exact hb
  have he := congrArg (fun bs : List Bool => bs.getD (owner i).val false) (forward_bits q)
  have hoi : (owner i).val < BinaryArithmetic.toNat q.ambient := (owner i).isLt
  have hlow : (⟨(owner i).val,hoi⟩ : Fin (BinaryArithmetic.toNat q.ambient)) ∉ H := by
    simpa [List.getD_eq_getElem?_getD, hoi] using he.symm.trans hmask
  change (⟨(owner i).val,hoi⟩ : Fin (BinaryArithmetic.toNat q.ambient)) ∉ H
  exact hlow

/-- Changing factor IDs to physical ambient-offset addresses preserves the
owner in each actual saved plan position. -/
theorem plans_owner (i : Fin (s).plans.length) :
    ((s).plans.get i).1 = (owner (Fin.cast (s).plans_length i)).val := by
  unfold ProducedQueryRank.owner PackingIncidenceInput.Semantics.owner
  have hn : i.val < (PackingIncidenceInput.Semantics.nativeEntries
      (p).scopes (p).mask).length := (Fin.cast (s).plans_length i).isLt
  have ha : i.val < (PackingIncidenceInput.addressedEntries
      (p).scopes (p).n (p).mask).length := by
    simpa only [PackingIncidenceInput.addressedEntries_length] using hn
  have ha' : i.val < ((PackingIncidenceInput.Semantics.nativeEntries
      (p).scopes (p).mask).map (fun x => (x.1,(p).n+x.2))).length := by
    simpa only [List.length_map] using hn
  change ((PackingIncidenceInput.addressedEntries (p).scopes (p).n (p).mask)[i.val]'ha).1 =
    ((PackingIncidenceInput.Semantics.nativeEntries (p).scopes (p).mask)[i.val]'hn).1
  change (((PackingIncidenceInput.Semantics.nativeEntries (p).scopes (p).mask).map
    (fun x => (x.1,(p).n+x.2)))[i.val]'ha').1 =
      ((PackingIncidenceInput.Semantics.nativeEntries (p).scopes (p).mask)[i.val]'hn).1
  rw [List.getElem_map]


section Produced
open SubexpLiftRing SubexpQuarticRing
variable (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (words : List (List Bool))
    (hc : CacheCorrect (Native.queryInputsAddressed q k hg first tail node).height (unary (Native.queryInputsAddressed q k hg first tail node).R) (Native.queryInputsAddressed q k hg first tail node).width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : (Native.queryInputsAddressed q k hg first tail node).Q < 3^(m.val 34)) (hv : q.Valid) (J : ℕ) (hJ : 0 < J)
    (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed q k hg first tail node).n))))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)
local notation "spec" => LeafProgram.PreparedSource.nativeSpecOfInputs s m ht hd words hc
  M cache half e hp hfield q hv J hJ source hsource
local notation "sourceOwner" => owner ∘ Fin.cast (Native.Inputs.plans_length s)
include m ht hd words hc M cache half e hp hfield hv J hJ source hsource

theorem produced_owner_head (i : Fin (spec).ps.length) (t : Fin (p).Q) :
    ((spec).packing.label i).head t = head t (sourceOwner i) := by
  have hps : (spec).ps.length=(s).plans.length := rfl
  let i' : Fin (s).plans.length := Fin.cast hps i
  change ((PackingIncidenceInput.reindexPacking (s).plans_length.symm
    (s).packing).label i').head t = _
  rw [PackingIncidenceInput.reindexPacking_label]
  have ho : owner (Fin.cast (s).plans_length i') = sourceOwner i := Fin.ext rfl
  exact (owner_head q k hg first tail node (Fin.cast (s).plans_length i') t).trans
    (congrArg (head t) ho)

theorem produced_owner_low (i : Fin (spec).ps.length) : sourceOwner i ∉ H :=
  owner_low q k hg (Fin.cast (s).plans_length i)

/-- The source factory uses the same original integer matrix; only the
proof-level row index is transported to the actual saved plan-list length. -/
theorem produced_literal (j v : ℕ) :
    LayoutProducedMatrix.literalNat (spec).packing sourceOwner
      (spec).p.aWord.length (spec).p.R node j v =
      LayoutProducedMatrix.literalNat (s).packing owner (s).height.length (s).R node j v := by
  change LayoutProducedMatrix.literalNat
    (PackingIncidenceInput.reindexPacking (s).plans_length.symm (s).packing)
    (owner ∘ Fin.cast (s).plans_length) (s).height.length (s).R node j v = _
  exact SignatureKeySource.literalNat_reindex (s).plans_length.symm (s).packing owner
    (s).height.length (s).R node j v

/-- The actual loader's signed matrix and shift relation give the exact
source-factory coefficient words. The plan-owner alignment is proved from the
addressed constructor, including all raw rows and the actual column order. -/
theorem produced_shifted_typed
    (W : List Bool) (hW : BinaryArithmetic.toNat W=(s).offset)
    (g : Fin (p).r) (raw : List (List LayoutMatrixProgram.Pair))
    (shifted : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel (s).relation (s).columnLength (s).D
      (js g) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw shifted) :
    ∃ c : Fin (spec).ps.length →
        Fin (js g).length → List Bool,
      shifted=List.ofFn (fun j => List.ofFn (c j)) ∧
      ∀ j i,(BinaryArithmetic.toNat (c j i) : ℤ)=(BinaryArithmetic.toNat W : ℤ)+
        LayoutProducedMatrix.literalNat (spec).packing sourceOwner
          (spec).p.aWord.length (spec).p.R node j.val
          ((js g).get i) := by
  let ps : Fin (s).D → ℕ × ℕ := fun i => (s).plans.get (Fin.cast (s).plans_length.symm i)
  have hplans : (s).plans=List.ofFn ps :=
    (List.ofFn_get (s).plans).symm.trans (List.ofFn_congr (s).plans_length _)
  have hpowner : ∀ i,(ps i).1=(owner i).val := by
    intro i
    have h := plans_owner q k hg first tail node (Fin.cast (s).plans_length.symm i)
    change (ps i).1=(owner i).val
    have ho : owner (Fin.cast (s).plans_length (Fin.cast (s).plans_length.symm i))=
        owner i := Fin.ext rfl
    exact h.trans (congrArg Fin.val ho)
  obtain ⟨c,hrows,he⟩ := SignatureHeadLoader.native_shiftedMatrix_typed s W hW owner ps
    hplans hpowner (node.val*(p).r+g.val) raw shifted hr hy
  refine ⟨fun j => c (Fin.cast (s).plans_length j),?_,?_⟩
  · exact hrows.trans (List.ofFn_congr (s).plans_length.symm _)
  · intro j i
    rw [produced_literal q k hg first tail node m ht hd words hc M cache half e hp
      hfield hv J hJ source hsource]
    exact he (Fin.cast (s).plans_length j) i

/-- Every source row of the exact head label equals the raw integer key of
its actual cursor assignment. No row basis or coordinate tuple is substituted. -/
theorem ordered_source_key (g : Fin (p).r) (candidate : Fin (2^(js g).length)) :
    (fun j : Fin (s).D =>
      HeadSourceLocality.freeLabel (spec).p (spec).ps (spec).packing sourceOwner head H node g
        ((freeAssignmentEquiv H (fun v => head node v.val) g (js g)
          (selected_bound q k hg first tail node g)
          (selected_nodup q k hg first tail node g)
          (selected_spec q k hg first tail node g)).symm
          (AttainedSignatures.assignmentEquiv (js g).length candidate))
        (Fin.cast (s).plans_length.symm j)) =
      AttainedSignatures.integerKey
        (fun (j : Fin (s).D) (i : Fin (js g).length) =>
          LayoutProducedMatrix.literalNat (s).packing owner (s).height.length (s).R node
            j.val ((js g).get i)) candidate := by
  let order := freeOrder H (fun v => head node v.val) g (js g)
    (selected_bound q k hg first tail node g)
    (selected_nodup q k hg first tail node g)
    (selected_spec q k hg first tail node g)
  funext j
  let value := fun v : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g =>
    LayoutProducedMatrix.literalNat (spec).packing sourceOwner
      (spec).p.aWord.length (spec).p.R node j.val v.val.val.val *
        (if AttainedSignatures.assignmentEquiv (js g).length candidate (order.symm v)
          then 1 else 0 : ℤ)
  change (∑ v, value v) = _
  rw [← order.sum_comp value]
  unfold AttainedSignatures.integerKey LayoutSignatureBound.boolSignature
    LayoutExactBuckets.signature
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [value]
  rw [order.symm_apply_apply]
  change LayoutProducedMatrix.literalNat (spec).packing sourceOwner
      (spec).p.aWord.length (spec).p.R node j.val ((js g).get i) *
      (if AttainedSignatures.assignmentEquiv (js g).length candidate i then 1 else 0 : ℤ) = _
  exact congrArg (fun z : ℤ => z *
    (if AttainedSignatures.assignmentEquiv (js g).length candidate i then 1 else 0))
    (produced_literal q k hg first tail node m ht hd words hc M cache half e hp hfield
      hv J hJ source hsource j.val ((js g).get i))

/-- The canonical cursor and authentic source label have exactly the same
equality classes after every source row is retained. -/
theorem source_key_eq_iff (g : Fin (p).r) (x y : Fin (2^(js g).length)) :
    let label := fun candidate : Fin (2^(js g).length) =>
      HeadSourceLocality.freeLabel (spec).p (spec).ps (spec).packing sourceOwner head H node g
        ((freeAssignmentEquiv H (fun v => head node v.val) g (js g)
          (selected_bound q k hg first tail node g)
          (selected_nodup q k hg first tail node g)
          (selected_spec q k hg first tail node g)).symm
          (AttainedSignatures.assignmentEquiv (js g).length candidate))
    AttainedSignatures.integerKey
        (fun (j : Fin (s).D) (i : Fin (js g).length) =>
          LayoutProducedMatrix.literalNat (s).packing owner (s).height.length (s).R node
            j.val ((js g).get i)) x =
      AttainedSignatures.integerKey
        (fun (j : Fin (s).D) (i : Fin (js g).length) =>
          LayoutProducedMatrix.literalNat (s).packing owner (s).height.length (s).R node
            j.val ((js g).get i)) y ↔ label x = label y := by
  dsimp only
  rw [← ordered_source_key q k hg first tail node m ht hd words hc M cache half e hp hfield
    hv J hJ source hsource g x,
    ← ordered_source_key q k hg first tail node m ht hd words hc M cache half e hp hfield
      hv J hJ source hsource g y]
  exact row_cast_eq_iff (s).plans_length.symm _ _

/-- Canonical cursor representatives count precisely the attained full
source labels on this selected free head. No arbitrary row-coordinate grid
is introduced, and the assignment width remains the physical selected size. -/
theorem card_representatives_eq_labels (g : Fin (p).r) :
    Fintype.card (AttainedSignatures.Representative
      (AttainedSignatures.integerKey
        (fun (j : Fin (s).D) (i : Fin (js g).length) =>
          LayoutProducedMatrix.literalNat (s).packing owner (s).height.length (s).R node
            j.val ((js g).get i)))) =
      Nat.card (Set.range
        (HeadSourceLocality.freeLabel (spec).p (spec).ps (spec).packing sourceOwner
          head H node g)) := by
  let label := HeadSourceLocality.freeLabel (spec).p (spec).ps (spec).packing sourceOwner
    head H node g
  let assignments := (AttainedSignatures.assignmentEquiv (js g).length).trans
    (freeAssignmentEquiv H (fun v => head node v.val) g (js g)
      (selected_bound q k hg first tail node g)
      (selected_nodup q k hg first tail node g)
      (selected_spec q k hg first tail node g)).symm
  rw [← Nat.card_eq_fintype_card]
  calc
    _ = Nat.card (AttainedSignatures.Representative (label ∘ assignments)) :=
      SignatureTupleTraversal.card_representative_kernel _ _ (fun x y =>
        source_key_eq_iff q k hg first tail node m ht hd words hc M cache half e hp hfield
          hv J hJ source hsource g x y)
    _ = Nat.card (Set.range (label ∘ assignments)) :=
      AttainedSignatures.card_representative _
    _ = Nat.card (Set.range label) := by
      exact congrArg (fun X : Set _ => Nat.card X) (assignments.surjective.range_comp label)

/-- Equality of the actual emitted shifted keys is exactly equality of
complete source labels. The physical matrix witnesses come from the paid
loader; no separately supplied successful coefficient layout is needed. -/
theorem shifted_key_eq_iff
    (W : List Bool) (hW : BinaryArithmetic.toNat W=(s).offset)
    (g : Fin (p).r) (raw : List (List LayoutMatrixProgram.Pair))
    (shifted : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel (s).relation (s).columnLength (s).D (js g) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw shifted)
    (x y : Fin (2^(js g).length)) :
    AttainedSignatureProgram.Rescan.naturalKey W shifted (js g).length x.val =
      AttainedSignatureProgram.Rescan.naturalKey W shifted (js g).length y.val ↔
      HeadSourceLocality.freeLabel (spec).p (spec).ps (spec).packing sourceOwner head H node g
        ((freeAssignmentEquiv H (fun v => head node v.val) g (js g)
          (selected_bound q k hg first tail node g)
          (selected_nodup q k hg first tail node g)
          (selected_spec q k hg first tail node g)).symm
          (AttainedSignatures.assignmentEquiv (js g).length x)) =
      HeadSourceLocality.freeLabel (spec).p (spec).ps (spec).packing sourceOwner head H node g
        ((freeAssignmentEquiv H (fun v => head node v.val) g (js g)
          (selected_bound q k hg first tail node g)
          (selected_nodup q k hg first tail node g)
          (selected_spec q k hg first tail node g)).symm
          (AttainedSignatures.assignmentEquiv (js g).length y)) := by
  obtain ⟨c,hc,he⟩ := produced_shifted_typed q k hg first tail node m ht hd words hc
    M cache half e hp hfield hv J hJ source hsource W hW g raw shifted hr hy
  rw [hc]
  exact SignatureKeySource.naturalKey_eq_freeLabel (spec).p (spec).ps (spec).packing
    sourceOwner head H node g (js g)
    (selected_bound q k hg first tail node g)
    (selected_nodup q k hg first tail node g)
    (selected_spec q k hg first tail node g) W c he x y

end Produced
end Query
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSourceAlignment
end

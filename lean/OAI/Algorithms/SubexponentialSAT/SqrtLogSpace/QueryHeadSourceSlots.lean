import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceFacts
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteQueryPlan

/-! Actual addressed factor lookup and reindexed source packing have the
same factor slot. The physical selected factor lists are complete color
filters, including neutral factors for unused low variables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceSlots
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open MulticolorTypes Subexp.ConstructivePacking SubexpLiftRing SubexpQuarticRing
open LeafHeadSetupProgram LeafParametersProgram LayoutProgram LeafProgram
open SignatureTupleSourceAlignment
variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
local notation "p" => LeafProgram.Query.packingProblem q k hg
variable (first : Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q)
  (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem q k hg).Q)
local notation "s" => Native.queryInputsAddressed q k hg first tail node
variable (physical : Data)
  (ready : Native.Ready (Native.queryInputsAddressed q k hg first tail node) physical)
  (bound : ℕ) (bounded : OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound bound physical)
  (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
  (hc : CacheCorrect (Native.queryInputsAddressed q k hg first tail node).height
    (unary (Native.queryInputsAddressed q k hg first tail node).R)
    (Native.queryInputsAddressed q k hg first tail node).width words)

local notation "src" => QueryHeadSourceFacts.addressedSource q k hg first tail node physical ready bound bounded ra rd rc words hc
section Factor
variable (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : (Native.queryInputsAddressed q k hg first tail node).Q < 3^(m.val 34))
    (hv : q.Valid) (hJ : 0 < m.val 42)
    (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed q k hg first tail node).n))))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)
local notation "spec" => QueryReadyConstruction.sourceSpec src m ht hd M cache half e hp
  hfield q hv hJ source hsource
local notation "owner" => ProducedQueryRank.owner p
local notation "sourceOwner" => owner ∘ Fin.cast (Native.Inputs.plans_length s)
local notation "head" => (fun t v => ProducedQueryRank.words p first tail (Sum.inl v) t)
local notation "H" => HighMarkedFrontend.highSet q


/-- A retained source row uses exactly the actual produced factor word. -/
theorem source_slot (f : Fin (p).factors) (j : ℕ)
    (hj : (j,(s).n+f.val) ∈ (spec).ps) :
    ((spec).packing.label (LeafProgram.NodeConcrete.planIndex (spec).ps (s).n f.val j hj)).slot 0 node =
      ProducedQueryRank.words p first tail (.inr f) node := by
  change (j,(p).n+f.val) ∈
    PackingIncidenceInput.addressedEntries (p).scopes (p).n (p).mask at hj
  change ((PackingIncidenceInput.addressedPacking (p).scopes (p).n (p).mask
      (ProducedQueryRank.packing p first tail)).label
        (LeafProgram.NodeConcrete.planIndex
          (PackingIncidenceInput.addressedEntries (p).scopes (p).n (p).mask)
          (p).n f.val j hj)).slot 0 node = _
  simpa only [LeafProgram.NodeConcrete.planColor,dite_eq_left f.isLt] using
    LeafProgram.NodeConcrete.addressedPlan_slot p first tail node f.val j hj

/-- The original semantic factor-color map agrees with every actual source
lookup. The addressed plan stream itself proves the factor index is in range. -/
theorem source_color (f j : ℕ) (hj : (j,(s).n+f) ∈ (spec).ps) :
    ((spec).packing.label (LeafProgram.NodeConcrete.planIndex (spec).ps (s).n f j hj)).slot 0 node =
      LeafProgram.NodeConcrete.planColor p first tail node f := by
  exact LeafProgram.NodeConcrete.addressedPlan_slot p first tail node f j hj

/-- Exactly the premise used by signed_source_target for the complete actual
factor inventory; no slot/color hypothesis is supplied by its caller. -/
theorem inventory_slots :
    ∀ f ∈ List.range (s).N, ∀ j (hj : (j,(s).n+f) ∈ (spec).ps),
      ((spec).packing.label (LeafProgram.NodeConcrete.planIndex (spec).ps (s).n f j hj)).slot 0 node =
        LeafProgram.NodeConcrete.planColor p first tail node f := by
  intro f _ j hj
  exact source_color q k hg first tail node physical ready bound bounded ra rd rc words hc
    m ht hd M cache half e hp hfield hv hJ source hsource f j hj

/-- The actual671 factor records, copied once to175, are exactly the original
semantic color filter of the complete ambient factor inventory. -/
theorem factorIds_eq_color (g : Fin (p).r) :
    QueryVisitorHead.factorIds s g =
      (List.range (s).N).filter (fun f => LeafProgram.NodeConcrete.planColor p first tail node f = g) := by
  change LeafHeadFactorsProgram.chosenIds
    (LeafHeadFactorsProgram.predicate (s).rows (s).n (node.val*(p).r+g.val)) (s).N = _
  rw [factor_ids q k hg first tail node g]
  apply List.filter_congr
  intro f hf
  have hlt : f < (p).factors := List.mem_range.mp hf
  simp only [LeafProgram.NodeConcrete.planColor,dite_eq_left hlt]

/-- Every retained incidence of a physically selected factor is owned by
that same color group; repeated incidences keep their original list position. -/
theorem selected_factor_slots (g : Fin (p).r) (f : ℕ)
    (hf : f ∈ QueryVisitorHead.factorIds s g) (j : ℕ) (hj : (j,(s).n+f) ∈ (spec).ps) :
    ((spec).packing.label (LeafProgram.NodeConcrete.planIndex (spec).ps (s).n f j hj)).slot 0 node = g := by
  have hlt : f < (p).factors := by
    exact LeafHeadFactorsProgram.chosenIds_bound
      (LeafHeadFactorsProgram.predicate (s).rows (s).n (node.val*(p).r+g.val))
      (s).N f hf
  have hword : ProducedQueryRank.words p first tail (.inr ⟨f,hlt⟩) node = g :=
    (factor_selected_mem q k hg first tail node g ⟨f,hlt⟩).1 hf
  refine (source_color q k hg first tail node physical ready bound bounded ra rd rc words hc
    m ht hd M cache half e hp hfield hv hJ source hsource f j hj).trans ?_
  unfold LeafProgram.NodeConcrete.planColor
  rw [dite_eq_left hlt]
  exact Fin.ext (congrArg Fin.val hword)

end Factor
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceSlots

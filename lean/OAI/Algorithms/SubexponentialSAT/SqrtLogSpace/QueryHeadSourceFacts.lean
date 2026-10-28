import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSourceAlignment
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteRows

/-! The actual addressed query source fixes the native layout and factor
specification together. Its semantic facts require no independent source,
selected-head, integer-matrix or successful-layout alignment premise. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceFacts
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

/-- Physical output data of the actual addressed loader and cache producer,
with the semantic owners and plans fixed by that same addressed constructor. -/
def addressedSource : SignatureTupleSource.ProducedSource where
  input := s
  source := physical
  ready := ready
  bound := bound
  bounded := bounded
  rows := query_rows_length q k hg first tail node
  owner := ProducedQueryRank.owner p
  plans := fun i => (s).plans.get (Fin.cast (s).plans_length.symm i)
  plans_eq := (List.ofFn_get (s).plans).symm.trans (List.ofFn_congr (s).plans_length _)
  owners_eq := by
    intro i
    have h := plans_owner q k hg first tail node (Fin.cast (s).plans_length.symm i)
    change ((s).plans.get (Fin.cast (s).plans_length.symm i)).1 =
      (ProducedQueryRank.owner p i).val
    have ho : ProducedQueryRank.owner p
        (Fin.cast (s).plans_length (Fin.cast (s).plans_length.symm i)) =
        ProducedQueryRank.owner p i := Fin.ext rfl
    exact h.trans (congrArg Fin.val ho)
  addressRegisters := ra
  dimensionRegisters := rd
  cacheRegisters := rc
  cacheWords := words
  cache := hc

local notation "src" => addressedSource q k hg first tail node physical ready bound bounded ra rd rc words hc

/-- The physical source constructor retains every actual loader/cache word;
only the proof-level plans and owners are reconstructed from the same input. -/
theorem addressedSource_data :
    (src).input = s ∧ (src).source = physical ∧ (src).cacheWords = words ∧
      (src).owner = ProducedQueryRank.owner p := ⟨rfl,rfl,rfl,rfl⟩

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

/-- All fixed-high coordinates vanish in the actual addressed source rows.
The physical plan list contains only low owners, including repeated incidences. -/
theorem source_high_zero (id j : ℕ) (v : Fin (s).n) (hvH : v ∈ H) :
    PerturbationAssembly.fixedSourceRow (spec).p (spec).ps (spec).packing (s).n id j v = 0 := by
  apply LeafProgram.NodeConcrete.fixedSourceRow_zero
  intro a ha he
  obtain ⟨i,hi,hia⟩ := List.mem_iff_getElem.mp ha
  have ho := plans_owner q k hg first tail node ⟨i,hi⟩
  change ((spec).ps.get ⟨i,hi⟩).1 = (sourceOwner ⟨i,hi⟩).val at ho
  simp only [List.get_eq_getElem,hia] at ho
  have hev : sourceOwner ⟨i,hi⟩ = v := Fin.ext (ho.symm.trans he)
  have hvowner : sourceOwner ⟨i,hi⟩ ∈ H := hev.symm ▸ hvH
  exact owner_low q k hg (Fin.cast (s).plans_length ⟨i,hi⟩) hvowner

/-- Concrete semantic certificate for the actual one-head visitor, generated
from one addressed ProducedSource and its authentic sourceSpec factory. -/
theorem sourceFacts : QueryVisitorHead.SourceFacts (src).input spec H
    sourceOwner (src).owner head where
  dimension := (s).plans_length
  plans_owner := plans_owner q k hg first tail node
  literal := produced_literal q k hg first tail node m ht hd words hc M cache half e hp
    hfield hv (m.val 42) hJ source hsource
  selected := selected_spec q k hg first tail node
  source_zero := source_high_zero q k hg first tail node physical ready bound bounded
    ra rd rc words hc m ht hd M cache half e hp hfield hv hJ source hsource
  rows_length := query_rows_length q k hg first tail node

/-- The query shadow erases only source storage outside the native masters.
The actual one-head source facts therefore hold after the same physical rebase. -/
theorem sourceFacts_shadow (B : ℕ)
    (hb : ∀ i, ¬ (i.val = 320 ∨ i.val = 322 ∨ i.val = 770 ∨ i.val = 771 ∨ i.val = 781) →
      ((src).source.stacks i).length ≤ B) :
    QueryVisitorHead.SourceFacts (QueryReadyConstruction.shadowSource src B hb).input
      (QueryReadyConstruction.sourceSpec (QueryReadyConstruction.shadowSource src B hb)
        m ht hd M cache half e hp hfield q hv hJ source hsource) H
      sourceOwner (QueryReadyConstruction.shadowSource src B hb).owner head :=
  sourceFacts q k hg first tail node physical ready bound bounded ra rd rc words hc
    m ht hd M cache half e hp hfield hv hJ source hsource

end Factor
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceFacts

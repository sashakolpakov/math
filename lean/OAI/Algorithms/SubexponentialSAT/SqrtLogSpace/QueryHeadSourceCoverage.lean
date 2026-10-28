import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceSlots
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteQueryLiterals

/-! Every actual hash and marked factor is retained, and every low literal
in its interpreted source has its real ambient-address incidence. This uses
the same sourceSpec and complete factor inventory as the native visitor. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage
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



/-- The source factory retains every original hash row exactly once. -/
theorem weighted_rows_length :
    (AssignmentConcrete.weightedHashes spec).length = q.rows.length := by
  change ((PreparedSource.castRows (congrArg List.length hsource) q.rows).map
    (HashInputProgram.Expansion.weightedRow (m.val 33) (m.val 34) source)).length = q.rows.length
  simp only [List.length_map,PreparedSource.castRows_length]

/-- The actual scope counter includes all original hashes and every neutral
factor appended for low variables. -/
theorem inventory_hashes :
    ∀ id < (AssignmentConcrete.weightedHashes spec).length, id ∈ List.range (s).N := by
  intro id hid
  rw [weighted_rows_length] at hid
  have hs := PackingIncidenceInput.Semantics.counter_mono q.scopeRows q.forward 0 q.scopeRows.length
  change q.scopeRows.length ≤ (p).factors at hs
  rw [LeafQueryFrontend.Query.scopeRows,HashScopeProgram.Complete.scopes_length] at hs
  apply List.mem_range.mpr
  change id < (p).factors
  omega

/-- A present marked factor occupies its actual index after the hash rows. -/
theorem inventory_marked :
    (spec).marked = true → (AssignmentConcrete.weightedHashes spec).length ∈ List.range (s).N := by
  intro hm
  change q.mark.isSome = true at hm
  rw [weighted_rows_length]
  have hs := PackingIncidenceInput.Semantics.counter_mono q.scopeRows q.forward 0 q.scopeRows.length
  change q.scopeRows.length ≤ (p).factors at hs
  rw [LeafQueryFrontend.Query.scopeRows,HashScopeProgram.Complete.scopes_length,hm] at hs
  simp only [Bool.toNat_true] at hs
  apply List.mem_range.mpr
  change q.rows.length < (p).factors
  omega

/-- The physical forward mask recognizes precisely the actual free variables. -/
theorem low_word (v : Fin (s).n) (hvH : v ∉ H) : q.forward.getD v.val false = false := by
  have hv : v.val < BinaryArithmetic.toNat q.ambient := v.isLt
  let v' : Fin (BinaryArithmetic.toNat q.ambient) := ⟨v.val,hv⟩
  have hv' : v' = v := Fin.ext rfl
  rw [forward_bits q]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hv),
    List.getElem_ofFn]
  have hnot : v' ∉ H := hv'.symm ▸ hvH
  exact decide_eq_false hnot

/-- Every low literal of an actual interpreted weighted hash has a saved
incidence. Zero ternary weights and repeated literals retain their raw scope. -/
theorem hash_literals :
    ∀ id ∈ List.range (s).N, ∀ hi : id < (AssignmentConcrete.weightedHashes spec).length,
      ∀ w ∈ (AssignmentConcrete.weightedHashes spec)[id], ∀ l ∈ w.literals,
        l.variable ∉ H → (l.variable.val,(s).n+id) ∈ (spec).ps := by
  intro id _ hi w hw l hl hlow
  exact LeafProgram.NodeConcrete.query_weighted_literal_present q hv source hsource
    (m.val 33) (m.val 34) id hi w hw l hl
    (low_word q k hg first tail node l.variable hlow)

/-- The actual optional marked clause has the same saved low-literal
incidences, at the index immediately following all original hashes. -/
theorem marked_literals :
    (spec).marked = true → (AssignmentConcrete.weightedHashes spec).length ∈ List.range (s).N →
      ∀ l ∈ (spec).markedClause, l.variable ∉ H →
        (l.variable.val,(s).n+(AssignmentConcrete.weightedHashes spec).length) ∈ (spec).ps := by
  intro hm _ l hl hlow
  rw [weighted_rows_length]
  exact LeafProgram.NodeConcrete.query_marked_clause_present q hv source hsource hm l hl
    (low_word q k hg first tail node l.variable hlow)

end Factor
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage

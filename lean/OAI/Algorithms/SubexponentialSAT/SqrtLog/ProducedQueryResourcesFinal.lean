import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesValues
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesSetup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesInitial

namespace OAI.Algorithms

/-! One fixed resource constructor for actual generated queries. Its setup
constants come from native startup/construction, its ordinary exponent from
all-port numeric bounds, and its geometry from the actual searched packing.
All bounds use one uniform cutoff over queries, marks and padding. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter Asymptotic LeafQueryFrontend
open scoped Topology
open SubexponentialSAT.MulticolorTypes
noncomputable section

 def ordinaryExponent : ℕ := Classical.choose exists_value_cap
 theorem ordinaryExponent_ge : 13 ≤ ordinaryExponent := (Classical.choose_spec exists_value_cap).1

 def resources (q : Query) (k B qi : ℕ) (hg : LeafParametersProgram.Guard (q.input k))
    (a : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q)) : CostAssembly.Resources :=
  ofPacking q k B setupC setupD qi ordinaryExponent hg a tail

 theorem values_le_resources (q : Query) (k B qi n : ℕ) (hn : 2 ≤ n)
    (hqn : ambient q=n) (hs : SmallInputs q k n)
    (hg : LeafParametersProgram.Guard (q.input k))
    (a : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q))
    (l : Fin 8 → ℕ) (j : Fin 64) :
    (LeafParametersProgram.Circuit.result LeafParametersProgram.Serialization.code
      (LeafParametersProgram.Execute.guardedModel (q.input k) l)).val j ≤
      (resources q k B qi hg a tail).bits :=
  (Classical.choose_spec exists_value_cap).2 q k B setupC setupD qi n hn hqn hs hg a tail l j

 theorem eventually_resources_bounds (k qi : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B : ℕ), q.Valid → ambient q=n →
      Origin q k B → 0 < B → q.clauses.length ≤ n*B → B ≤ L n^qi →
      LeafParametersProgram.Guard (q.input k) ∧ SmallInputs q k n ∧
      ∀ (hg : LeafParametersProgram.Guard (q.input k))
        (a : Word (problem q k hg).r (problem q k hg).Q)
        (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
        (a::tail).Nodup → (∀z,z∈a::tail) →
        CostAssembly.Bounds qi (LeafScopeResourceBounds.resourceExponent qi+1)
          (9*ordinaryExponent+8) n (resources q k B qi hg a tail) :=
  eventually_ofPacking_bounds k qi setupC setupD ordinaryExponent

/-- The remaining initial-occurrence premise is discharged by the executed
splitter. A nonempty generated query has positive occurrence automatically.
Empty and contradictory branches are handled before making such a query. -/
 theorem fixed_width_resources (k T : ℕ) :
    ∃ qi N : ℕ, ∀ n ≥ N, ∀ F : SAT.CNF (Fin n), SAT.WidthAtMost k F →
      ∀ G ∈ SparsifyDyadic.liveLeaves k T (s n) F,
      ∀ q : Query, q.Valid → ambient q=n → q.clauses.length=G.card →
      Origin q k (SparsifyDyadic.occurrenceBound k T (s n)) →
      LeafParametersProgram.Guard (q.input k) ∧ SmallInputs q k n ∧
      ∀ (hg : LeafParametersProgram.Guard (q.input k))
        (a : Word (problem q k hg).r (problem q k hg).Q)
        (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
        (a::tail).Nodup → (∀z,z∈a::tail) →
        CostAssembly.Bounds qi (LeafScopeResourceBounds.resourceExponent qi+1)
          (9*ordinaryExponent+8) n
          (resources q k (SparsifyDyadic.occurrenceBound k T (s n)) qi hg a tail) := by
  obtain ⟨qi,hi⟩ := initial_leaf_bounds k T
  have h : ∀ᶠ n : ℕ in atTop, ∀ F : SAT.CNF (Fin n), SAT.WidthAtMost k F →
      ∀ G ∈ SparsifyDyadic.liveLeaves k T (s n) F,
      ∀ q : Query, q.Valid → ambient q=n → q.clauses.length=G.card →
      Origin q k (SparsifyDyadic.occurrenceBound k T (s n)) →
      LeafParametersProgram.Guard (q.input k) ∧ SmallInputs q k n ∧
      ∀ (hg : LeafParametersProgram.Guard (q.input k))
        (a : Word (problem q k hg).r (problem q k hg).Q)
        (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
        (a::tail).Nodup → (∀z,z∈a::tail) →
        CostAssembly.Bounds qi (LeafScopeResourceBounds.resourceExponent qi+1)
          (9*ordinaryExponent+8) n
          (resources q k (SparsifyDyadic.occurrenceBound k T (s n)) qi hg a tail) := by
    filter_upwards [hi,eventually_resources_bounds k qi] with n hi hr F hF G hG q hv hqn hc o
    obtain ⟨_,hcount,hB,hpos⟩ := hi F hF G hG
    exact hr q _ hv hqn o (hpos (by rw [←hc]; exact o.nonempty)) (by simpa only [hc] using hcount) hB
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp h
  exact ⟨qi,N,hN⟩

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms

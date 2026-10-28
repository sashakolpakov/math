import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutInput

namespace OAI.Algorithms

/-!
# Boundedness of the actual emitted scope pattern

The proof uses the same unary-then-clause enumeration as the scope producer.
In particular, the factor degree includes the unary factor for each chunk.
-/

namespace SubexponentialSAT.SubexpMainLayoutPattern

open SubexpMainProgram SubexpPackingParameters
open SubexpMainLayoutInput

theorem raw_bounded {n ell p k B : ℕ} [Fact p.Prime]
    (G : SubexpLeafData.Leaf n) (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (hk : 1 ≤ k)
    (hwidth : SAT.WidthAtMost k (ExecCNF.formulaSet G))
    (hocc : SAT.OccurrenceAtMost B (ExecCNF.formulaSet G)) (hne : [] ∉ G) :
    (Subexp.IncidencePlanSpec.pattern (ChunkPartition.count n ell)
      (SubexpLeafScopeOrder.rawScopes G hG hell)).Bounded k (1 + ell * B) := by
  have hb := SubexpLEFactorSystem.packed_bounded hell hcap (ExecCNF.formulaSet G)
    hk hwidth hocc (SubexpLeafData.clauses_nonempty G hne)
  exact Subexp.OrderedScopeSystem.bounded
    (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G))
    (SubexpLeafData.factors G hG)
    (SubexpLeafData.scopes G hG (ChunkPartition.indexEquiv n ell hell))
    (SubexpLeafData.scopes_mem G hG (ChunkPartition.indexEquiv n ell hell)
      (PackedSAT.capacity (n := n) hcap)) hb

theorem ordered_bounded {p k B : ℕ} [Fact p.Prime]
    (x : SubexpLayoutConstruction.Inputs)
    (G : SubexpLeafData.Leaf (SubexpLayoutConstruction.variableCount x))
    (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < CounterPrograms.value x.counts.ell)
    (hD : SubexpLayoutConstruction.dimension x = ChunkPartition.count
      (SubexpLayoutConstruction.variableCount x) (CounterPrograms.value x.counts.ell))
    (hcap : 2 ^ CounterPrograms.value x.counts.ell ≤ p) (hk : 1 ≤ k)
    (hwidth : SAT.WidthAtMost k (ExecCNF.formulaSet G))
    (hocc : SAT.OccurrenceAtMost B (ExecCNF.formulaSet G)) (hne : [] ∉ G) :
    (Subexp.IncidencePlanSpec.pattern (SubexpLayoutConstruction.dimension x)
      (SubexpLayoutScopeOrder.orderedScopes x G hG hell)).Bounded k
      (1 + CounterPrograms.value x.counts.ell * B) := by
  rw [hD]
  exact raw_bounded G hG hell hcap hk hwidth hocc hne

/-- The complete bounded-pattern premise for the semantic layout follows
from the very input facts used by the actual layout execution. -/
theorem bounded {er es n k T : ℕ} [Fact (p n).Prime]
    (alloc : SubexpLayoutPorts.Allocation es) (a : MainState er es)
    (G : SubexpLeafData.Leaf n) (input : Ready alloc a n k T G) (hk : 1 ≤ k) :
    (Subexp.IncidencePlanSpec.pattern
      (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))
      (SubexpLayoutScopeOrder.orderedScopes (SubexpMainLayout.Factors.sourceInputs alloc a)
        (castLeaf input.variableCount.symm G) input.sparse.clause_sets_nodup input.ell_pos)).Bounded
      k (DyadicSchedule.delta k T n) := by
  have hb := ordered_bounded (SubexpMainLayout.Factors.sourceInputs alloc a)
    (castLeaf input.variableCount.symm G) input.sparse.clause_sets_nodup input.ell_pos
    input.dimension input.capacity hk input.sparse.width input.sparse.occurrences input.no_empty
  exact ⟨hb.nonempty_scope, hb.arity_le, fun v => (hb.incidence_le v).trans input.delta⟩

end SubexponentialSAT.SubexpMainLayoutPattern

end OAI.Algorithms

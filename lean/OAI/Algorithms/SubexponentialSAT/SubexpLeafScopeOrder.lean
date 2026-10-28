import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpClauseScopeCorrectness
import OAI.Algorithms.SubexponentialSAT.SubexpClauseFamilyProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.OrderedScopeSystem

namespace OAI.Algorithms

/-!
# Scope payloads and degree in the physical leaf order

The unary prefix and clause-family outputs have exactly the factor order
used by the semantic system. Inner scope order is the actual last-occurrence
order; only membership is used by the incidence counter.
-/

namespace SubexponentialSAT.SubexpLeafScopeOrder

open Subexp.OrderedScopeSystem Subexp.IncidencePlanSpec

variable {n ell p k B : ℕ}

def rawScopes (G : SubexpLeafData.Leaf n) (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < ell) : List (List ℕ) :=
  Subexp.OrderedScopeSystem.rawScopes (SubexpLeafData.factors G hG)
    (SubexpLeafData.scopes G hG (ChunkPartition.indexEquiv n ell hell))

private theorem unary_values (D : ℕ) :
    ((List.finRange D).map (fun j => [j])).map (List.map Fin.val) =
      (List.range D).map List.singleton := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_coe_finRange D, List.map_map]
  rfl

theorem rawScopes_eq_stream (G : SubexpLeafData.Leaf n)
    (hG : (G.map ExecCNF.clauseSet).Nodup) (hell : 0 < ell) :
    rawScopes G hG hell =
      (List.range (ChunkPartition.count n ell)).map List.singleton ++
      (G.map (SubexpLeafData.clauseScope (ChunkPartition.indexEquiv n ell hell))).map
        (List.map Fin.val) := by
  have h := congrArg (List.map (List.map Fin.val))
    (SubexpLeafData.scope_stream G hG (ChunkPartition.indexEquiv n ell hell))
  rw [List.map_append, unary_values] at h
  simpa only [rawScopes, Subexp.OrderedScopeSystem.rawScopes, List.map_map,
    Function.comp_def] using h

theorem family_scopes_eq (c : SubexpClauseFamilyProgram.Inputs)
    (hv : SubexpClauseFamilyProgram.Valid c
      (ChunkPartition.count n (BinaryArithmetic.toNat c.binaryEll)) n)
    (G : SubexpLeafData.Leaf n) :
    SubexpClauseFamilyProgram.scopes c G =
      (G.map (SubexpLeafData.clauseScope
        (ChunkPartition.indexEquiv n (BinaryArithmetic.toNat c.binaryEll) hv.ell_pos))).map
          (fun scope => Encoding.encodeList Encoding.encodeNat (scope.map Fin.val)) := by
  simp only [SubexpClauseFamilyProgram.scopes, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro ls hls
  exact SubexpClauseScopeCorrectness.scopeBytes_eq_canonical
    (SubexpClauseFamilyCallback.withClause c ls) ls hv.ell_pos
    (SubexpClauseFamilyCallback.validClause c hv ls)

/-- The actual family payload stream is the encoding of the ordered scopes. -/
theorem payloads_eq_rawScopes (c : SubexpClauseFamilyProgram.Inputs)
    (hv : SubexpClauseFamilyProgram.Valid c
      (ChunkPartition.count n (BinaryArithmetic.toNat c.binaryEll)) n)
    (G : SubexpLeafData.Leaf n) (hG : (G.map ExecCNF.clauseSet).Nodup) :
    ((List.range (ChunkPartition.count n (BinaryArithmetic.toNat c.binaryEll))).map
      List.singleton).map (Encoding.encodeList Encoding.encodeNat) ++
        SubexpClauseFamilyProgram.scopes c G =
      (rawScopes G hG hv.ell_pos).map (Encoding.encodeList Encoding.encodeNat) := by
  rw [rawScopes_eq_stream, List.map_append, family_scopes_eq c hv G]
  simp only [List.map_map, Function.comp_def]

section Bounded

variable [Fact p.Prime]

/-- Reindexing into the emitted factor order preserves the actual incidence
bound, including the one unary factor per chunk. -/
theorem degree_le (G : SubexpLeafData.Leaf n) (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (hk : 1 ≤ k)
    (hwidth : SAT.WidthAtMost k (ExecCNF.formulaSet G))
    (hocc : SAT.OccurrenceAtMost B (ExecCNF.formulaSet G)) (hnoempty : [] ∉ G)
    (v : Fin (ChunkPartition.count n ell)) :
    Subexp.IncidencePlanSpec.degree (rawScopes G hG hell) v.val ≤ 1 + ell * B := by
  have hb := SubexpLEFactorSystem.packed_bounded hell hcap (ExecCNF.formulaSet G)
    hk hwidth hocc (SubexpLeafData.clauses_nonempty G hnoempty)
  exact Subexp.OrderedScopeSystem.degree_le
    (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G))
    (SubexpLeafData.factors G hG)
    (SubexpLeafData.scopes G hG (ChunkPartition.indexEquiv n ell hell))
    (SubexpLeafData.scopes_mem G hG (ChunkPartition.indexEquiv n ell hell)
      (PackedSAT.capacity (n := n) hcap)) hb v

end Bounded

end SubexponentialSAT.SubexpLeafScopeOrder

end OAI.Algorithms

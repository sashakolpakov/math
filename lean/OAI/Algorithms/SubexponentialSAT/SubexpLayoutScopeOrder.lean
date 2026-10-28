import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutConstruction
import OAI.Algorithms.SubexponentialSAT.SubexpLeafScopeOrder

namespace OAI.Algorithms

/-!
# Scope bytes and incidence bounds for the actual layout constructor

Both statements use the same typed leaf and canonical chunk positions. The
actual constructor's scope payloads are exactly the encoded ordered scopes;
their incident-factor degree is at most one unary factor plus ell*B.
-/

namespace SubexponentialSAT.SubexpLayoutScopeOrder

open SubexpLayoutConstruction

abbrev orderedScopes (x : Inputs)
    (G : SubexpLeafData.Leaf (variableCount x))
    (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < CounterPrograms.value x.counts.ell) : List (List ℕ) :=
  SubexpLeafScopeOrder.rawScopes G hG hell

theorem canonicalValid (x : Inputs)
    (hv : SubexpClauseFamilyProgram.Valid (familyInputs x) (dimension x) (variableCount x))
    (hD : dimension x = ChunkPartition.count (variableCount x)
      (CounterPrograms.value x.counts.ell)) :
    SubexpClauseFamilyProgram.Valid (familyInputs x)
      (ChunkPartition.count (variableCount x)
        (BinaryArithmetic.toNat (familyInputs x).binaryEll)) (variableCount x) := by
  have hD' : dimension x = ChunkPartition.count (variableCount x)
      (BinaryArithmetic.toNat (familyInputs x).binaryEll) := by
    simpa only [familyInputs, CounterPrograms.value_eq_toNat] using hD
  exact hD' ▸ hv

/-- Every payload, including every singleton unary scope, has the required
semantic factor position. No encoded list is introduced as free input. -/
theorem scope_payloads_eq (x : Inputs)
    (hv : SubexpClauseFamilyProgram.Valid (familyInputs x) (dimension x) (variableCount x))
    (G : SubexpLeafData.Leaf (variableCount x))
    (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < CounterPrograms.value x.counts.ell)
    (hD : dimension x = ChunkPartition.count (variableCount x)
      (CounterPrograms.value x.counts.ell)) :
    SubexpLayoutConstruction.scopes x G =
      (orderedScopes x G hG hell).map (Encoding.encodeList Encoding.encodeNat) := by
  have h := SubexpLeafScopeOrder.payloads_eq_rawScopes (familyInputs x)
    (canonicalValid x hv hD) G hG
  have he : (familyInputs x).binaryEll = x.counts.ell := rfl
  simpa only [SubexpLayoutConstruction.scopes, prefixScopes, orderedScopes,
    he, CounterPrograms.value_eq_toNat, List.range_eq_range'] using h

/-- The exact byte stream read by the incidence-plan constructor. -/
theorem scope_stream_eq (x : Inputs)
    (hv : SubexpClauseFamilyProgram.Valid (familyInputs x) (dimension x) (variableCount x))
    (G : SubexpLeafData.Leaf (variableCount x))
    (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < CounterPrograms.value x.counts.ell)
    (hD : dimension x = ChunkPartition.count (variableCount x)
      (CounterPrograms.value x.counts.ell)) :
    Encoding.encodeList id (SubexpLayoutConstruction.scopes x G) =
      Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) (orderedScopes x G hG hell) := by
  rw [scope_payloads_eq x hv G hG hell hD, SubexpLayoutConstruction.encodeList_map]

theorem orderedScopes_length (x : Inputs)
    (G : SubexpLeafData.Leaf (variableCount x))
    (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < CounterPrograms.value x.counts.ell) :
    (orderedScopes x G hG hell).length =
      ChunkPartition.count (variableCount x) (CounterPrograms.value x.counts.ell) + G.length := by
  rw [orderedScopes, SubexpLeafScopeOrder.rawScopes_eq_stream]
  simp only [List.length_append, List.length_map, List.length_range]

section Bounded

variable {p k B : ℕ} [Fact p.Prime]

/-- The assignment-side degree bound is obtained from the actual packed
factor system and transported to exactly the constructor's scope order. -/
theorem degree_le (x : Inputs) (G : SubexpLeafData.Leaf (variableCount x))
    (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < CounterPrograms.value x.counts.ell)
    (hD : dimension x = ChunkPartition.count (variableCount x)
      (CounterPrograms.value x.counts.ell))
    (hcap : 2 ^ CounterPrograms.value x.counts.ell ≤ p) (hk : 1 ≤ k)
    (hwidth : SAT.WidthAtMost k (ExecCNF.formulaSet G))
    (hocc : SAT.OccurrenceAtMost B (ExecCNF.formulaSet G)) (hnoempty : [] ∉ G)
    (v : Fin (dimension x)) :
    Subexp.IncidencePlanSpec.degree (orderedScopes x G hG hell) v.val ≤
      1 + CounterPrograms.value x.counts.ell * B := by
  have hv : v.val < ChunkPartition.count (variableCount x)
      (CounterPrograms.value x.counts.ell) := by simpa only [hD] using v.isLt
  exact SubexpLeafScopeOrder.degree_le G hG hell hcap hk hwidth hocc hnoempty ⟨v.val, hv⟩

end Bounded

end SubexponentialSAT.SubexpLayoutScopeOrder

end OAI.Algorithms

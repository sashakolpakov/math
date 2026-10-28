import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainNodeArguments
import OAI.Algorithms.SubexponentialSAT.SubexpNodeUniformBound
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutWordBounds
import OAI.Algorithms.SubexponentialSAT.SubexpWeightLiteralBase

namespace OAI.Algorithms

/-! Original node-input sizes from the actual layout and initialization
outputs. Large layout masters remain inside the supplied layout word bound.
The initialization and header execution costs are separate from this size
bound; no generated Taylor, template, exponent, or query stream is assumed
to have a bounded size here. -/

namespace SubexponentialSAT.SubexpMainNodeInputBounds

open scoped BigOperators
open SubexpMainProgram SubexpLiftRing
open SubexpLayoutPorts (Allocation ordinary master)
open SubexpMainMomentData (store target)
open SubexpMainNodeArguments (source rowExpr cache)
open SubexpMainLayoutWordBounds

noncomputable section

def scale (W p D R r : ℕ) : ℕ :=
  W + p + D + R + r + (p ^ 4 - 1) + baseWidth p (D + 1) + baseWidth p 1 +
    SubexpSymbolicCost.indexBits D + 1

theorem scale_components (W p D R r : ℕ) :
    W ≤ scale W p D R r ∧ p ≤ scale W p D R r ∧ D ≤ scale W p D R r ∧
    R + 1 ≤ scale W p D R r ∧ r ≤ scale W p D R r ∧
    p ^ 4 - 1 ≤ scale W p D R r ∧ baseWidth p (D + 1) ≤ scale W p D R r ∧
    baseWidth p 1 ≤ scale W p D R r ∧
    SubexpSymbolicCost.indexBits D ≤ scale W p D R r ∧ 1 ≤ scale W p D R r := by
  unfold scale
  omega

private theorem scope_sum_le_bytes (scopes : List (List ℕ)) :
    (scopes.map List.length).sum ≤
      (Encoding.encodeList SubexpFactorPrefixProgram.scopeBytes scopes).length := by
  induction scopes with
  | nil => simp
  | cons scope scopes ih =>
      have hs := Encoding.length_encodeList_lower Encoding.encodeNat scope
      change scope.length + 1 ≤ (SubexpFactorPrefixProgram.scopeBytes scope).length at hs
      rw [Encoding.length_encodeList_cons]
      simp only [List.map_cons, List.sum_cons]
      omega

variable {er es p r Δ R D W : ℕ} [Fact p.Prime] [NeZero r]
  {alloc : Allocation es} {a middle layoutOut initialized : MainState er es}
  {hregs : 16 ≤ er} {hr : 0 < r} {hQ : 0 < p ^ 4 - 1}
  {scopes : List (List ℕ)}
  {hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ}
  {tables : List (List Bool)}
  (h : SubexpMainLayoutExecution.Result hregs alloc a middle layoutOut
    p r Δ R D hr hQ scopes hd tables)
  (hi : SubexpMainNodeInitialization.Result alloc
    (SubexpMainNodeSetup.prepared alloc layoutOut) initialized D)
  (hW : RelevantWordBound W layoutOut)

omit [Fact p.Prime] [NeZero r] in
include hi hW in
theorem static_word_le (i : Fin 32) :
    (store alloc initialized ⟨256 + i.val, by omega⟩).length ≤ W := by
  rw [SubexpMainMomentData.static_frame hi i]
  exact ordinary hW alloc ⟨640 + i.val, by omega⟩

omit [Fact p.Prime] [NeZero r] in
include hi hW in
theorem source_word_le (i : Fin 10) :
    (store alloc initialized ⟨128 + i.val, by omega⟩).length ≤ W := by
  rw [SubexpMainMomentData.source_frame hi i]
  exact ordinary hW alloc ⟨128 + i.val, by omega⟩

omit [Fact p.Prime] [NeZero r] in
include hi hW in
theorem row_word_le : (store alloc initialized 255).length ≤ W := by
  rw [SubexpMainMomentData.row_frame hi]
  exact ordinary hW alloc 255

omit [Fact p.Prime] [NeZero r] in
include hi hW in
theorem radius_word_le : (store alloc initialized 126).length ≤ W := by
  rw [SubexpMainMomentHeaders.radius_copied hi]
  exact ordinary hW alloc 243

include h hi hW in
theorem selected_master_le (i : Fin 288)
    (hm : i ∈ Subexp.NodeCanonicalScale.masterPorts) :
    (store alloc initialized i).length ≤ 27 * scale W p D R r := by
  obtain ⟨hws, _, _, _, _, _, hB, _, hI, h1⟩ := scale_components W p D R r
  have hs (j : Fin 32) :
      (store alloc initialized ⟨256 + j.val, by omega⟩).length ≤ 27 * scale W p D R r := by
    have hb := static_word_le (p := p) (r := r) hi hW j
    omega
  have hb (j : Fin 10) :
      (store alloc initialized ⟨128 + j.val, by omega⟩).length ≤ 27 * scale W p D R r := by
    have ht := source_word_le (p := p) (r := r) hi hW j
    omega
  simp only [Subexp.NodeCanonicalScale.masterPorts, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [SubexpMainMomentData.target_modulus h hi]
    have hm := (target p D).modulus.length_le
    omega
  · rw [SubexpMainMomentData.target_width h hi]
    omega
  · rw [SubexpMainMomentHeaders.target_reduction h hi, SubexpQuarticFlatMul.flat_length]
    omega
  · rw [SubexpMainMomentData.target_minusOne h hi]
    have hl := (SubexpPreparedQuarticSetup.minusOne p (D + 1)).property
    rw [hl]
    omega
  · rw [SubexpMainMomentData.raw_zero hi]
    simp only [List.length_singleton]
    omega
  · rw [SubexpMainMomentData.raw_one h hi, SubexpWeightLiteralProgram.rawLiteral_length,
      SubexpQuarticFlatMul.flat_length]
    omega
  · rw [SubexpMainMomentData.unit_word h hi, fixedBits_length]
    omega
  · have ht := radius_word_le hi hW
    omega
  · exact hb 0
  · exact hb 1
  · exact hb 2
  · exact hb 3
  · have ht := row_word_le hi hW
    omega
  · exact hs 2
  · exact hs 5
  · exact hs 8
  · exact hs 10
  · exact hs 13
  · exact hs 14
  · exact hs 15
  · exact hs 16
  · exact hs 20
  · exact hs 21
  · exact hs 23
  · exact hs 24
  · exact hs 26
  · exact hs 27

include h hi hW in
theorem masterVolume_le :
    Subexp.NodeCanonicalScale.masterVolume (store alloc initialized) ≤ 729 * scale W p D R r := by
  have hc : Subexp.NodeCanonicalScale.masterPorts.card = 27 := by decide
  calc
    _ ≤ ∑ _i ∈ Subexp.NodeCanonicalScale.masterPorts, 27 * scale W p D R r := by
      exact Finset.sum_le_sum (fun i hm => selected_master_le h hi hW i hm)
    _ = _ := by simp only [Finset.sum_const, hc, smul_eq_mul]; omega

include h hi hW in
theorem original_words_le :
    (source h).modulus.bits.length ≤ W ∧
    (ProgramEncoding.encodeRecords
      (SubexpNodeLiftData.liftedNodeWords p (D + 1) (source h).modulus)).length ≤ W ∧
    (Encoding.encodeList SubexpFactorPrefixProgram.scopeBytes scopes).length ≤ W ∧
    (Encoding.encodeList id tables).length ≤ W ∧
    (Subexp.FactorPacketCoordinates.cacheBytes
      ((cache h).map (List.map SubexpQuarticFlatNeg.flat))).length ≤ W := by
  have hc := SubexpMainMomentData.context_masters h hi
  have hp := SubexpMainNodeArguments.packet_masters h hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change h.rows.cacheFacts.source.modulus.bits.length ≤ W
    rw [← hc.sourceModulus]
    exact source_word_le (p := p) (r := r) hi hW 0
  · rw [← SubexpMainNodeArguments.node_master h hi, SubexpMainMomentData.nodes_from_layout hi]
    exact ordinary hW alloc 300
  · rw [← hp.scopes]
    exact static_word_le (p := p) (r := r) hi hW 0
  · rw [← hp.tables]
    exact static_word_le (p := p) (r := r) hi hW 1
  · rw [← hp.lagrange]
    exact static_word_le (p := p) (r := r) hi hW 28

include h hi hW in
theorem row_count_le :
    (SubexpDenseRowTableSemantics.expressionRows (rowExpr h) D 0 scopes).length ≤ W := by
  rw [SubexpDenseRowTableSemantics.expressionRows_length]
  exact (scope_sum_le_bytes scopes).trans (original_words_le h hi hW).2.2.1

include h hi hW in
/-- The exact uniform scale consumed by the node-worker cost theorem. The
layout-output bound may itself contain the cost of the actual layout run. -/
theorem uniformSize_le_linear :
    SubexpNodeUniformBound.uniformSize p D R r
      (SubexpDenseRowTableSemantics.expressionRows (rowExpr h) D 0 scopes).length
      (store alloc initialized)
      (SubexpNodeLiftData.liftedNodeWords p (D + 1) (source h).modulus)
      (source h).modulus.bits
      (SubexpQuarticFlatNeg.flat (target p D).zero)
      (SubexpQuarticFlatNeg.flat (target p D).one)
      scopes tables ((cache h).map (List.map SubexpQuarticFlatNeg.flat)) ≤
      1000 * scale W p D R r := by
  have hm := masterVolume_le h hi hW
  obtain ⟨hmod, hnodes, hscopes, htables, hcache⟩ := original_words_le h hi hW
  have hrows := row_count_le h hi hW
  obtain ⟨hws, hps, hds, hrs, hrr, hQ, hB, hb, hI, h1⟩ := scale_components W p D R r
  unfold SubexpNodeUniformBound.uniformSize Subexp.NodeCanonicalScale.originalSize
    Subexp.NodeCacheBounds.scale
  simp only [List.length_replicate, SubexpQuarticFlatNeg.flat_length]
  omega

include h hi hW in
theorem uniformSize_bound :
    SubexpNodeUniformBound.uniformSize p D R r
      (SubexpDenseRowTableSemantics.expressionRows (rowExpr h) D 0 scopes).length
      (store alloc initialized)
      (SubexpNodeLiftData.liftedNodeWords p (D + 1) (source h).modulus)
      (source h).modulus.bits
      (SubexpQuarticFlatNeg.flat (target p D).zero)
      (SubexpQuarticFlatNeg.flat (target p D).one)
      scopes tables ((cache h).map (List.map SubexpQuarticFlatNeg.flat)) ≤
      1000 * (scale W p D R r) ^ 2 :=
  (uniformSize_le_linear h hi hW).trans
    (Nat.mul_le_mul_left 1000 (Nat.le_self_pow (by decide) _))

end
end SubexponentialSAT.SubexpMainNodeInputBounds

end OAI.Algorithms

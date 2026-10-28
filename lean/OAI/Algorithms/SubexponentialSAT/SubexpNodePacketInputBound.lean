import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodePacketBoundaryBound
import OAI.Algorithms.SubexponentialSAT.SubexpNodePacketReady
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCacheTyped
import OAI.Algorithms.SubexponentialSAT.Subexp.NodeOriginBytes

namespace OAI.Algorithms

/-! The packet producer's origin and Taylor streams are bounded from the
actual preceding computations. Its size no longer contains either generated
stream as an independent input-size premise. -/

namespace SubexponentialSAT.SubexpNodePacketInputBound

open SubexpLiftRing SubexpSelectedConversions

abbrev Bits := List Bool

def staticSize (p μ R N C m : ℕ) (modulus zero one : Bits)
    (scopes : List (List ℕ)) (tables : List Bits) (cache : List (List Bits)) : ℕ :=
  Subexp.NodeCacheBounds.scale m C R N (baseWidth p μ) (baseWidth p 1) modulus.length +
  (Encoding.encodeList SubexpFactorPrefixProgram.scopeBytes scopes).length +
  (Encoding.encodeList id tables).length + (Subexp.FactorPacketCoordinates.cacheBytes cache).length +
  modulus.length + zero.length + one.length + 1

variable (p μ : ℕ) [Fact p.Prime]
variable (source : Prepared p 0) (target : SubexpPreparedQuartic.Modulus p μ)
variable (reduction theta : SubexpTaylorRow.Code p μ)
variable (R N : ℕ) (hN : 0 < N)
variable (width : Bits) (hw : width.length = baseWidth p 1)
variable (es : List (List (SubexpTaylorRowCorrectness.RowExpr p)))
variable (scopes : List (List ℕ)) (tables : List Bits) (cache : List (List Bits)) (zero one : Bits)

/-- The scope/table/scalar cache words are original masters; only their
literal lengths occur in `staticSize`. The two node-generated streams are
replaced by the checked origin/Taylor output estimates. -/
theorem inputSize_le (C : ℕ) (hC : ∀ row ∈ es, row.length ≤ C) :
    SubexpFactorPacketBounds.inputSize
      (SubexpNodePacketReady.inputs p μ source target reduction theta R N hN width hw
        es scopes tables cache zero one) ≤
      79 * (staticSize p μ R N C es.length source.modulus.bits zero one scopes tables cache)^4 := by
  let K := Subexp.NodeCacheBounds.scale es.length C R N
    (baseWidth p μ) (baseWidth p 1) source.modulus.bits.length
  let S := staticSize p μ R N C es.length source.modulus.bits zero one scopes tables cache
  let i := SubexpNodePacketReady.inputs p μ source target reduction theta R N hN width hw
    es scopes tables cache zero one
  have hS : 1 ≤ S := by dsimp [S, staticSize]; omega
  have hKS : K ≤ S := by dsimp [K, S, staticSize]; omega
  have hK3 : K^3 ≤ S^4 :=
    (Nat.pow_le_pow_left hKS 3).trans (Nat.pow_le_pow_right hS (by decide))
  have hK4 : K^4 ≤ S^4 := Nat.pow_le_pow_left hKS 4
  have hS4 : S ≤ S^4 := Nat.le_self_pow (by decide) S
  have horigins : (Encoding.encodeList (Encoding.encodeList id) i.origins).length ≤ 25 * K^3 := by
    rw [SubexpNodePacketReady.origins_bytes]
    change (Encoding.encodeList (Encoding.encodeList SubexpFlatLift.encode)
      (SubexpOriginCacheSemantics.origins p μ source target reduction theta R N hN
        source.modulus width hw es)).length ≤ _
    rw [← SubexpOriginCacheSemantics.outputBytes_cacheRows]
    apply Subexp.NodeOriginBytes.outputBytes_le p source.modulus width hw
      (SubexpOriginCacheSemantics.cacheRows p μ source target reduction theta R N hN es)
      es.length C R N (baseWidth p μ) (baseWidth p 1) source.modulus.bits.length
    · simp [SubexpOriginCacheSemantics.cacheRows]
    · intro row hrow
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hrow
      simpa only [List.length_map] using hC old ho
    · exact le_rfl
  have hcolumns : (Encoding.encodeList (Encoding.encodeList (Encoding.encodeList id)) i.columns).length ≤
      53 * K^4 := by
    rw [SubexpNodePacketReady.columns_bytes, ← SubexpNodeCacheTyped.cache_bytes]
    apply Subexp.NodeCacheBounds.cacheBytes_le p μ target reduction theta
      es.length C R N (baseWidth p μ) (baseWidth p 1) source.modulus.bits.length
      (SubexpNodeCacheTyped.rows p μ source R es)
    · simpa only [SubexpNodeCacheTyped.rows_length] using (le_rfl : es.length ≤ es.length)
    · exact SubexpNodeCacheTyped.rows_width p μ source R C es hC
    · exact le_rfl
  have hother : (Encoding.encodeList SubexpFactorPrefixProgram.scopeBytes i.scopes).length +
      (Encoding.encodeList id i.tables).length + (Subexp.FactorPacketCoordinates.cacheBytes i.cache).length +
      i.modulus.length + i.zero.length + i.one.length + 1 ≤ S := by
    dsimp [i, SubexpNodePacketReady.inputs, S, staticSize]
    omega
  have ho4 := horigins.trans (Nat.mul_le_mul_left 25 hK3)
  have hc4 := hcolumns.trans (Nat.mul_le_mul_left 53 hK4)
  change SubexpFactorPacketBounds.inputSize i ≤ 79 * S^4
  unfold SubexpFactorPacketBounds.inputSize SubexpFactorPrefixProgram.inputBytes
  omega

end SubexponentialSAT.SubexpNodePacketInputBound

end OAI.Algorithms

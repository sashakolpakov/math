import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeTemplateSuffixBound

namespace OAI.Algorithms

/-! Assemble the separately proved component estimates. The packet estimate
below calls the actual input/output producer bounds; `sum_bounds` is the
final natural-number arithmetic rule used with the worker's trace witnesses. -/

namespace SubexponentialSAT.SubexpNodeCostAssembly

open SubexpNodeOriginalInputBound SubexpLiftRing SubexpSelectedConversions

theorem coefficient_ge {a : ℕ} (ha : a ≤ 10^78) : a ≤ coefficient := by
  have hpow : 1 ≤ (20000000000 : ℕ)^48 := Nat.one_le_pow _ _ (by norm_num)
  have h := Nat.mul_le_mul_left (10^78) hpow
  exact ha.trans (by simpa only [Nat.mul_one, coefficient] using h)

private theorem promote (S J X a u v : ℕ) (hS : 1 ≤ S) (hJ : 1 ≤ J) (hX : 1 ≤ X)
    (ha : a ≤ coefficient) (hu : u ≤ 768) (hv : v ≤ 8) :
    a * S^u * J^v ≤ coefficient * S^768 * X * J^8 := by
  calc
    _ ≤ coefficient * S^768 * J^8 := Nat.mul_le_mul
      (Nat.mul_le_mul ha (Nat.pow_le_pow_right hS hu)) (Nat.pow_le_pow_right hJ hv)
    _ = coefficient * S^768 * 1 * J^8 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hX)

def scale (prelude packet suffix : ℕ) : ℕ := prelude + packet + suffix + 1

/-- The three bounds are supplied by the prelude, original packet-input,
and combined template/moment theorems. All final control halts are included. -/
theorem sum_bounds (preludeCost packetCost suffixCost preludeSize packetSize suffixSize J D : ℕ)
    (hJ : 1 ≤ J)
    (hp : preludeCost ≤ 10^20 * preludeSize^20 * J^4)
    (hk : packetCost ≤ (100000 * 79^5) * packetSize^20)
    (hs : suffixCost ≤ 4 * coefficient * suffixSize^768 * 2^(128*D) * J^8) :
    preludeCost + packetCost + suffixCost + 1 ≤
      7 * coefficient * (scale preludeSize packetSize suffixSize)^768 * 2^(128*D) * J^8 := by
  let S := scale preludeSize packetSize suffixSize
  let X := 2^(128*D)
  let K := coefficient * S^768 * X * J^8
  have hS : 1 ≤ S := by dsimp [S, scale]; omega
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (by decide)
  have hpS : preludeSize ≤ S := by dsimp [S, scale]; omega
  have hkS : packetSize ≤ S := by dsimp [S, scale]; omega
  have hsS : suffixSize ≤ S := by dsimp [S, scale]; omega
  have hpK : preludeCost ≤ K := by
    apply hp.trans
    apply le_trans (Nat.mul_le_mul_right (J^4)
      (Nat.mul_le_mul_left (10^20) (Nat.pow_le_pow_left hpS 20)))
    exact promote S J X (10^20) 20 4 hS hJ hX (coefficient_ge (by norm_num)) (by decide) (by decide)
  have hkK : packetCost ≤ K := by
    apply hk.trans
    apply le_trans (Nat.mul_le_mul_left (100000 * 79^5) (Nat.pow_le_pow_left hkS 20))
    simpa only [pow_zero, Nat.mul_one] using
      promote S J X (100000 * 79^5) 20 0 hS hJ hX
        (coefficient_ge (by norm_num)) (by decide) (by decide)
  have hsK : suffixCost ≤ 4 * K := by
    apply hs.trans
    have hpow := Nat.pow_le_pow_left hsS 768
    have h := Nat.mul_le_mul_right (J^8) (Nat.mul_le_mul_right X
      (Nat.mul_le_mul_left (4 * coefficient) hpow))
    simpa only [K, X, Nat.mul_assoc] using h
  have hK : 1 ≤ K := by
    have hc := coefficient_ge (a := 1) (by norm_num)
    have h := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.mul_le_mul hc (Nat.one_le_pow 768 S hS)) hX)
      (Nat.one_le_pow 8 J hJ)
    simpa only [one_mul] using h
  have hsum : preludeCost + packetCost + suffixCost + 1 ≤ 7 * K := by omega
  simpa only [K, S, X, Nat.mul_assoc] using hsum

section Packet

variable (p μ : ℕ) [Fact p.Prime]
variable (source : Prepared p 0) (target : SubexpPreparedQuartic.Modulus p μ)
variable (reduction theta : SubexpTaylorRow.Code p μ)
variable (R N : ℕ) (hN : 0 < N) (width : List Bool) (hw : width.length = baseWidth p 1)
variable (es : List (List (SubexpTaylorRowCorrectness.RowExpr p)))
variable (scopes : List (List ℕ)) (tables : List (List Bool))
variable (cache : List (List (List Bool))) (zero one : List Bool)

local notation "Input" => SubexpNodePacketReady.inputs p μ source target reduction theta R N hN
  width hw es scopes tables cache zero one

theorem packetRuntime_le (C : ℕ) (hC : ∀ row ∈ es, row.length ≤ C)
    (heq : (Input).origins.length = (Input).columns.length)
    (hincidence : ((Input).scopes.map List.length).sum = (Input).origins.length)
    (hm : 0 < BinaryArithmetic.toNat (Input).modulus)
    (hcache : BinaryArithmetic.toNat (Input).modulus ≤ (Input).cache.length) :
    SubexpFactorPacketProgram.runtimeBound Input ≤ (100000 * 79^5) *
      (SubexpNodePacketInputBound.staticSize p μ R N C es.length source.modulus.bits
        zero one scopes tables cache)^20 := by
  have hi := SubexpNodePacketInputBound.inputSize_le p μ source target reduction theta R N hN
    width hw es scopes tables cache zero one C hC
  apply (SubexpFactorPacketBounds.runtimeBound_le Input heq hincidence hm hcache).trans
  calc
    _ ≤ 100000 * (79 * (SubexpNodePacketInputBound.staticSize p μ R N C es.length source.modulus.bits
        zero one scopes tables cache)^4)^5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hi 5)
    _ = _ := by ring

end Packet

end SubexponentialSAT.SubexpNodeCostAssembly

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeTemplateIterationBound
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPacketBounds

namespace OAI.Algorithms

/-! The packet-stage output cap is derived from its original encoded input
streams and then substituted in the raw-template boundary. -/

namespace SubexponentialSAT.SubexpNodePacketBoundaryBound

open Subexp.ConstructivePacking SubexpNodeTemplateIterationBound

variable {p D r Q Δ : ℕ}

def originalSize (i : SubexpFactorPacketProgram.Inputs)
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix old226 : List Bool) : ℕ :=
  SubexpFactorPacketBounds.inputSize i +
  (SubexpFactorRoutingTraversal.words items ++ suffix).length +
  (Subexp.SupportSelectionProgram.metadataTable packing).length + old226.length +
  D + Q + r + Subexp.MatrixWordEncoding.width p + 1

theorem originalSize_pos (i : SubexpFactorPacketProgram.Inputs)
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix old226 : List Bool) :
    1 ≤ originalSize (p := p) i packing items suffix old226 := by
  unfold originalSize
  omega

/-- The only output premise is the exact byte identity established by
`output_eq_typedFactors` and `NodePacketRaw.packet_bytes`; its length is
derived here. The two scratch facts are the actual packet endpoint. -/
theorem boundarySize_le (i : SubexpFactorPacketProgram.Inputs)
    (heq : i.origins.length = i.columns.length)
    (hsize : (i.scopes.map List.length).sum = i.origins.length)
    (hm : 0 < BinaryArithmetic.toNat i.modulus)
    (hcache : BinaryArithmetic.toNat i.modulus ≤ i.cache.length)
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix old226 : List Bool)
    (store : SubexpRawTemplate.Store)
    (hpackets : Encoding.encodeList id (items.map Prod.snd) = SubexpFactorPacketProgram.output i)
    (h226 : store 226 = old226) (h227 : store 227 = []) :
    boundarySize (p := p) packing items suffix store ≤
      301 * (originalSize (p := p) i packing items suffix old226)^4 := by
  let S := originalSize (p := p) i packing items suffix old226
  have hS : 1 ≤ S := originalSize_pos i packing items suffix old226
  have hi : SubexpFactorPacketBounds.inputSize i ≤ S := by dsimp [S, originalSize]; omega
  have ho := (SubexpFactorPacketBounds.output_length_le i heq hsize hm hcache).trans
    (Nat.mul_le_mul_left 300 (Nat.pow_le_pow_left hi 4))
  have hrest : boundarySize (p := p) packing items suffix store ≤
      (SubexpFactorPacketProgram.output i).length + S := by
    unfold boundarySize
    rw [hpackets, h226, h227]
    dsimp [S, originalSize]
    omega
  have hS4 : S ≤ S^4 := Nat.le_self_pow (by decide) S
  change _ ≤ 301 * S^4
  omega

theorem packetRuntime_le (i : SubexpFactorPacketProgram.Inputs)
    (heq : i.origins.length = i.columns.length)
    (hsize : (i.scopes.map List.length).sum = i.origins.length)
    (hm : 0 < BinaryArithmetic.toNat i.modulus)
    (hcache : BinaryArithmetic.toNat i.modulus ≤ i.cache.length)
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix old226 : List Bool) :
    SubexpFactorPacketProgram.runtimeBound i ≤
      100000 * (originalSize (p := p) i packing items suffix old226)^5 := by
  apply (SubexpFactorPacketBounds.runtimeBound_le i heq hsize hm hcache).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  unfold originalSize
  omega

end SubexponentialSAT.SubexpNodePacketBoundaryBound

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopeProduced
import OAI.Algorithms.SubexponentialSAT.SqrtLog.FactorResourceCapacity

namespace OAI.Algorithms

/-! Fixed polynomial storage bounds. The work variable pays exponential
inventories; it is never classified as an ordinary input dimension. -/
namespace SubexponentialSAT.SqrtLog.NodeEnvelope
open SubexponentialSAT LeafProgram LeafProgram.NodeNative MomentsAssembly

theorem streamCap_polynomial (n input rCap H K U : ℕ) (hU : 1 ≤ U)
    (hn : n ≤ U) (hi : input ≤ U) (hr : rCap ≤ U) (hh : 2^H ≤ U) (hk : K ≤ U) :
    streamCap n input rCap H K ≤ 10000000000*U^8 := by
  have hu1 : U ≤ U^4 := by simpa using Nat.pow_le_pow_right hU (show 1 ≤ 4 by decide)
  have hu2 : U^2 ≤ U^4 := Nat.pow_le_pow_right hU (by decide)
  have hu3 : U^3 ≤ U^4 := Nat.pow_le_pow_right hU (by decide)
  have hu0 : 1 ≤ U^4 := Nat.one_le_pow _ _ hU
  have hinner : U+1+(2*(U*(4*U+20*(7*U+2)^2+4*(U*(2*U+1))+7))+2)*U+1 ≤ 4000*U^4 := by
    nlinarith
  unfold streamCap
  calc
    _ ≤ 502*(U+1+(2*(U*(4*U+20*(7*U+2)^2+4*(U*(2*U+1))+7))+2)*U+1)^2 := by gcongr
    _ ≤ 502*(4000*U^4)^2 := by gcongr
    _ ≤ 10000000000*U^8 := by nlinarith [Nat.zero_le (U^8)]

theorem assignmentCap_polynomial (s : HeadInputs) (input H K B d u J U : ℕ)
    (hU : 1 ≤ U) (hi : input ≤ U) (hn : s.n ≤ U) (hr : s.R ≤ U)
    (hw : s.width.length ≤ U) (hqr : s.Q*s.r ≤ U) (hh : 2^H ≤ U) (hk : K ≤ U)
    (hs : SupportProgram.count s.n J ≤ U)
    (he : dictionaryByteEnvelope B d (s.n+u+J)
      (dictionaryCapacity (Finset.univ : Finset (Fin s.n)) u J) ≤ 10*U^5) :
    assignmentCap s input (streamCap s.n input (s.Q*s.r) H K) B d u J ≤
      10000000000000000*U^8 := by
  have hstream := streamCap_polynomial s.n input (s.Q*s.r) H K U hU hn hi hqr hh hk
  have hwidth : s.R*s.width.length ≤ U^2 := by simpa only [pow_two] using Nat.mul_le_mul hr hw
  have hsupport : SupportProgram.count s.n J*(2*s.n+1) ≤ U*(2*U+1) := by gcongr
  have hu1 : U ≤ U^8 := by simpa using Nat.pow_le_pow_right hU (show 1 ≤ 8 by decide)
  have hu2 : U^2 ≤ U^8 := Nat.pow_le_pow_right hU (by decide)
  have hu5 : U^5 ≤ U^8 := Nat.pow_le_pow_right hU (by decide)
  have hu0 : 1 ≤ U^8 := Nat.one_le_pow _ _ hU
  unfold assignmentCap memoryCap spaceBudget
  nlinarith

theorem three_sum_product (input V work : ℕ) :
    input+V+work+2 ≤ 2*(input+1)*(V+1)*(work+1) := by
  nlinarith [Nat.zero_le (input*V), Nat.zero_le (input*work),
    Nat.zero_le (V*work), Nat.zero_le (input*V*work)]

theorem polynomial_padding (A input V work : ℕ)
    (h : A ≤ 10000000000000000*(input+V+work+2)^8) :
    A ≤ 2560000000000000000*(input+1)^8*(V+1)^8*(work+1)^8 := by
  calc
    A ≤ 10000000000000000*(input+V+work+2)^8 := h
    _ ≤ 10000000000000000*(2*(input+1)*(V+1)*(work+1))^8 := by
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (three_sum_product input V work) _)
    _ = _ := by simp only [mul_pow]; ring

end SubexponentialSAT.SqrtLog.NodeEnvelope

end OAI.Algorithms

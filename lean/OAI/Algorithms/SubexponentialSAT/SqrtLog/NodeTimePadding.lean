import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.FactorAssembledCanonical

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.NodeTime
open LeafProgram.FactorResource

/-- One monomial pays the input tapes, sparse storage and the measured
assignment cost. Its exponents are fixed before all query inputs. -/
def combinedPadding (input V W e : ℕ) : ℕ :=
  paddingEnvelope input V W (8*e+8) (75*e+70) (9*e+8)

theorem padding_mono (input V W a b c a' b' c' : ℕ)
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    paddingEnvelope input V W a b c ≤ paddingEnvelope input V W a' b' c' := by
  unfold paddingEnvelope
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) ha)
    (Nat.pow_le_pow_right (by omega) hb)) (Nat.pow_le_pow_right (by omega) hc)

theorem combinedPadding_caps (input V W e : ℕ) :
    input ≤ combinedPadding input V W e ∧ V ≤ combinedPadding input V W e ∧
    W ≤ combinedPadding input V W e ∧ 1 ≤ combinedPadding input V W e ∧
    paddingEnvelope input V W 8 70 8 ≤ combinedPadding input V W e ∧
    paddingEnvelope input V W (8*e) (75*e) (9*e) ≤ combinedPadding input V W e := by
  have hi := padding_mono input V W 1 0 0 (8*e+8) (75*e+70) (9*e+8) (by omega) (by omega) (by omega)
  have hv := padding_mono input V W 0 1 0 (8*e+8) (75*e+70) (9*e+8) (by omega) (by omega) (by omega)
  have hw := padding_mono input V W 0 0 1 (8*e+8) (75*e+70) (9*e+8) (by omega) (by omega) (by omega)
  simp only [paddingEnvelope,pow_zero,pow_one,Nat.one_mul,Nat.mul_one] at hi hv hw
  change input+1 ≤ combinedPadding input V W e at hi
  change V+1 ≤ combinedPadding input V W e at hv
  change W+1 ≤ combinedPadding input V W e at hw
  exact ⟨by omega,by omega,by omega,by omega,
    padding_mono input V W _ _ _ _ _ _ (by omega) (by omega) (by omega),
    padding_mono input V W _ _ _ _ _ _ (by omega) (by omega) (by omega)⟩

theorem sum_padding (input V W A time C e : ℕ)
    (ha : A ≤ paddingEnvelope input V W 8 70 8)
    (ht : time ≤ C*(input+1)^(8*e)*(V+1)^(75*e)*(W+1)^(9*e)) :
    input+V+W+A+time+2 ≤ (C+6)*combinedPadding input V W e := by
  obtain ⟨hi,hv,hw,h1,hA,hT⟩ := combinedPadding_caps input V W e
  have htime : time ≤ C*combinedPadding input V W e := by
    apply ht.trans
    calc
      _ = C*paddingEnvelope input V W (8*e) (75*e) (9*e) := by unfold paddingEnvelope; ring
      _ ≤ _ := Nat.mul_le_mul_left _ hT
  have ha' := ha.trans hA
  nlinarith only [hi,hv,hw,h1,htime,ha']


/-- Keep coefficients and powers abstract while proving the normalization;
this avoids expanding a fixed large coefficient in downstream applications. -/
theorem padding_power (K C input V W a b c e : ℕ) :
    K*(C*paddingEnvelope input V W a b c)^e =
      (K*C^e)*(input+1)^(a*e)*(V+1)^(b*e)*(W+1)^(c*e) := by
  unfold paddingEnvelope
  simp only [mul_pow,←pow_mul]
  ring

end SubexponentialSAT.SqrtLog.NodeTime

end OAI.Algorithms

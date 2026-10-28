import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound

namespace OAI.Algorithms

/-! A shared source-byte budget for literal and universal-row branches. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceExpression

open SubexponentialSAT.Subexp UniversalRowSourceBound PolynomialExecutorProgram

theorem literal_length {B d : ℕ} (c : Coeff B d) :
    (SubexpKernelControl.pushWord (RingProgram.flat c)).length = 2 * (d * B) + 2 := by
  simp

theorem literal_length_le {B d S : ℕ} (c : Coeff B d) (hwidth : d * B ≤ S) :
    (SubexpKernelControl.pushWord (RingProgram.flat c)).length ≤ 2 * S + 2 := by
  rw [literal_length]
  omega

theorem linear_le_sourceLengthBound (S : ℕ) :
    2 * S + 2 ≤ sourceLengthBound S := by
  have hi : 2 * S + 2 ≤ inputBound S := by
    unfold inputBound rowBytes
    omega
  have hp : 0 < inputBound S := by omega
  unfold sourceLengthBound
  nlinarith

theorem literal_length_le_sourceLengthBound {B d S : ℕ}
    (c : Coeff B d) (hwidth : d * B ≤ S) :
    (SubexpKernelControl.pushWord (RingProgram.flat c)).length ≤ sourceLengthBound S :=
  (literal_length_le c hwidth).trans (linear_le_sourceLengthBound S)

theorem sourceLengthBound_mono : Monotone sourceLengthBound := by
  intro a b hab
  unfold sourceLengthBound inputBound rowBytes termBytes factorsBytes factorBytes
  gcongr

end SubexponentialSAT.SqrtLog.LayoutSourceExpression

end OAI.Algorithms

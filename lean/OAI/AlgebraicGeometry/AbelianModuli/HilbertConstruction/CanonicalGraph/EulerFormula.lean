import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.EulerPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.EulerSequence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EventualPolynomialScaling
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.EmbeddingEulerPositive

/-! # Euler Formula -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every tensor power of the original graph bundle has its exact Euler monomial. The original coefficient is positive; identifying it from the polarization type remains separate. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_tensorPower_euler
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) (m : ℕ) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom (A.graphBundle.tensorPower m).sheaf =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf * (m : ℤ) ^ g := by
  have : NeZero N := ⟨by omega⟩
  have ha : 1 < N * N := by
    have hh := Nat.mul_le_mul hN hN
    omega
  obtain ⟨P, hP⟩ := A.graphBundle_eulerPolynomial_exists
  have hp : ∃ b : ℕ, ∀ n, b ≤ n → P.eval (n : ℚ) = A.graphPowerEulerSequence 1 n :=
    ⟨0, fun n _ => by simpa only [PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEulerSequence, one_mul] using hP n⟩
  have hmono := EventualPolynomialScaling.eventualPolynomial_scaling_value_one (A.graphPowerEulerSequence 1)
    P (N * N) g ha (A.graphPowerEulerSequence_scaling hNk 1) hp
  have h := (hP m).symm
  rw [hmono, Polynomial.eval_monomial] at h
  have h1 := Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso A.abelian.scheme.hom
    A.graphBundle.tensorPowerOneIso
  apply Int.cast_injective (α := ℚ)
  simpa only [PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEulerSequence, one_mul, h1, Int.cast_mul, Int.cast_pow,
    Int.cast_natCast] using h

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_euler_pos (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    0 < CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf := by
  obtain ⟨E⟩ := A.graphBundle_isAmple_overAlgClosed.exists_powerProjectiveEmbedding
    A.abelian.scheme.hom
  have hp := A.graphBundle_embeddedPower_euler_pos hN hNk E
  rw [A.graphBundle_tensorPower_euler hN hNk E.degree] at hp
  have hpow : 0 ≤ (E.degree : ℤ) ^ g := pow_nonneg (Int.natCast_nonneg _) _
  nlinarith

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

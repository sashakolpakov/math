import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.LeviOperators
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Substitution

/-! # Levi Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.LeviComparison.CM

noncomputable section

/-! The actual Levi oscillator pair has the rational Levi matrix and
acts by a scalar times the exact rational coordinate substitution. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ScalarComparison.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.LeviOperators.CM
variable (n : ℕ)

theorem real_matrix (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) :
    (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (LeviOperators.CM.realOscillator n A))).val =
      Matrix.fromBlocks (A.val.map (algebraMap ℚ ℝ)) 0 0 ((A⁻¹).val.transpose.map (algebraMap ℚ ℝ)) := by
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap * (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic (LeviOperators.CM.realInput n A)).val *
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap = _
  rw [RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic_matrix, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap_conjugation,
    LeviOperators.CM.realInput_inv_val, LeviOperators.CM.realInput_val, Matrix.transpose_transpose, LeviOperators.CM.realUnit_val, LeviOperators.CM.realUnit_inv_val]
  rfl

theorem finite_matrix (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) :
    (Finite.FiniteOscillator.CM.projection (LeviOperators.CM.finiteOscillator n A)).val =
      Matrix.fromBlocks (A.val.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) 0 0 ((A⁻¹).val.transpose.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := by
  change Matrix.fromBlocks (@Units.val _ (LeviOperators.CM.finiteMatrixMonoid n) (LeviOperators.CM.finiteUnit n A)) 0 0 (@Units.val _ (LeviOperators.CM.finiteMatrixMonoid n) ((LeviOperators.CM.finiteUnit n A)⁻¹)).transpose = _
  rw [LeviOperators.CM.finiteUnit_val, LeviOperators.CM.finiteUnit_inv_val]
  rfl

theorem pair_matrix (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) :
    Adelic.ScalarComparison.CM.pairMatrix n (LeviOperators.CM.realOscillator n A) (LeviOperators.CM.finiteOscillator n A) =
      (Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose).map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) := by
  unfold Adelic.ScalarComparison.CM.pairMatrix
  rw [real_matrix, finite_matrix]
  apply Matrix.ext
  intro i j
  cases i <;> cases j
  all_goals first | rfl | exact (map_zero (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)).symm

def scalar (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) : ℂ := LeviOperators.CM.realScalar n A * LeviOperators.CM.finiteScalar n A

theorem operator_raw (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)).subtype.comp (Adelic.ScalarComparison.CM.pairOperator n (LeviOperators.CM.realOscillator n A) (LeviOperators.CM.finiteOscillator n A)).toLinearMap =
      scalar n A • Substitution.CM.raw A := by
  apply Adelic.FiniteOperators.CM.Sections.linear_ext
  intro f φ
  change (Adelic.ScalarComparison.CM.pairOperator n (LeviOperators.CM.realOscillator n A) (LeviOperators.CM.finiteOscillator n A) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ)).val = _
  rw [Adelic.ScalarComparison.CM.pairOperator, Adelic.ProductOperators.CM.operator_tensor]
  funext x
  change (Adelic.ScalarComparison.CM.realOperator n (LeviOperators.CM.realOscillator n A) f).val (fun i => (x i).1) *
    (Finite.FiniteOscillator.CM.action (LeviOperators.CM.finiteOscillator n A) φ).val (fun i => (x i).2) = _
  rw [LeviOperators.CM.real_apply, LeviOperators.CM.finite_apply]
  change (_ * f.val _) * (_ * φ.val _) = (LeviOperators.CM.realScalar n A * LeviOperators.CM.finiteScalar n A) *
    (f.val (fun i => ((A.val.transpose.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) *ᵥ x) i).1) *
      φ.val (fun i => ((A.val.transpose.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) *ᵥ x) i).2))
  rw [Substitution.CM.phase_fst, Substitution.CM.phase_snd]
  ring

theorem operator_apply (A : (Matrix (Fin n) (Fin n) ℚ)ˣ)
    (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)) (x : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    (Adelic.ScalarComparison.CM.pairOperator n (LeviOperators.CM.realOscillator n A) (LeviOperators.CM.finiteOscillator n A) F).val x =
      scalar n A * F.val ((A.val.transpose.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) *ᵥ x) :=
  congrFun (LinearMap.congr_fun (operator_raw n A) F) x

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.LeviComparison.CM

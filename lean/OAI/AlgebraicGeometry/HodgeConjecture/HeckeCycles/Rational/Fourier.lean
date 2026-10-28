import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Split
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ScalarComparison

/-! # Fourier -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Fourier.CM

noncomputable section

/-! The rational Weyl lift acts by the exact adelic Fourier integral.
Its scalar is fixed by the proved Poisson identity and nonzero theta value. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ScalarComparison.CM
variable (n : ℕ)

theorem real_fourier_operator : Adelic.ScalarComparison.CM.realOperator n (Real.BareGenerators.CM.fullFourier n) =
    Real.Fourier.CM.fourierEquiv n := by
  unfold Adelic.ScalarComparison.CM.realOperator
  rw [Real.BareGenerators.CM.fullFourier_action]
  rfl

theorem pair_fourier_operator : Adelic.ScalarComparison.CM.pairOperator n (Real.BareGenerators.CM.fullFourier n)
    (Finite.FiniteOscillator.CM.fourierOscillator (I := Fin n)) = Adelic.Fourier.CM.fourierEquiv n := by
  unfold Adelic.ScalarComparison.CM.pairOperator
  rw [real_fourier_operator]
  rfl

theorem real_fourier_matrix :
    (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1)
      (Real.BareGenerators.CM.fullFourier n))).val =
      Matrix.fromBlocks 0 (-1) 1 0 := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.e23_fourier_coordinates

theorem finite_fourier_matrix {I : Type*} [Fintype I] :
    (Finite.FiniteOscillator.CM.projection (Finite.FiniteOscillator.CM.fourierOscillator (I := I))).val =
      Matrix.fromBlocks 0 (-1) 1 0 := rfl

theorem pair_fourier_matrix : Adelic.ScalarComparison.CM.pairMatrix n (Real.BareGenerators.CM.fullFourier n)
    (Finite.FiniteOscillator.CM.fourierOscillator (I := Fin n)) = Matrix.fromBlocks 0 (-1) 1 0 := by
  unfold Adelic.ScalarComparison.CM.pairMatrix
  rw [real_fourier_matrix, finite_fourier_matrix]
  apply Matrix.ext
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j => rfl
    | inr j =>
      by_cases hij : i = j <;> simp [SymplecticProduct.CM.pairMatrix, hij]
      rfl
  | inr i =>
    cases j with
    | inl j =>
      by_cases hij : i = j <;> simp [SymplecticProduct.CM.pairMatrix, hij]
    | inr j => rfl

theorem action_eq_fourier (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ) (hγ : γ.val = Matrix.fromBlocks 0 (-1) 1 0) :
    Constructed.ConstructedAdelicGroup.CM.action n (Split.CM.split n γ) = Adelic.Fourier.CM.fourierEquiv n := by
  have hp : (Constructed.ConstructedAdelicGroup.CM.projection n (Split.CM.split n γ)).val =
      Adelic.ScalarComparison.CM.pairMatrix n (Real.BareGenerators.CM.fullFourier n)
        (Finite.FiniteOscillator.CM.fourierOscillator (I := Fin n)) := by
    rw [Split.CM.split_covers, pair_fourier_matrix]
    change γ.val.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) = _
    rw [hγ]
    simp [Matrix.fromBlocks_map]
    change (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ).mapMatrix (-1) = -1
    rw [map_neg, map_one]
  obtain ⟨c, _, hc⟩ := Adelic.ScalarComparison.CM.scalar n (Split.CM.split n γ)
    (Real.BareGenerators.CM.fullFourier n) Finite.FiniteOscillator.CM.fourierOscillator hp
  simp only [pair_fourier_operator] at hc
  let Φ := Theta.Nonzero.CM.test (Fin n)
  have hθ := Split.CM.theta_invariant n γ Φ
  rw [hc, map_smul] at hθ
  have hP : RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional (Adelic.Fourier.CM.fourierEquiv n Φ) = RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional Φ :=
    Constructed.Poisson.CM.theta_fourier_invariant n Φ
  rw [hP] at hθ
  have hc1 : c = 1 := by
    apply mul_right_cancel₀ (Theta.Nonzero.CM.theta_ne_zero (Fin n))
    change c * RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional Φ = 1 * RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional Φ
    rw [one_mul]
    exact hθ
  apply LinearEquiv.ext
  intro F
  rw [hc, hc1, one_smul]

theorem rational_fourier (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ) (hγ : γ.val = Matrix.fromBlocks 0 (-1) 1 0)
    (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)) (x : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    (Constructed.ConstructedAdelicGroup.CM.action n (Split.CM.split n γ) F).val x =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier Constructed.AdelicCharacter.CM.character
        (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure (Constructed.FiniteMeasure.CM.measure (Fin n))) F.val x := by
  rw [action_eq_fourier n γ hγ]
  exact Adelic.Fourier.CM.fourierEquiv_apply n F x

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Fourier.CM

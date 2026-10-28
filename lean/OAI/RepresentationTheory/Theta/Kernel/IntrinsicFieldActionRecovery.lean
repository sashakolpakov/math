import OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianActionRecovery
import OAI.RepresentationTheory.Weil.Local.FieldOscillator

/-! # Intrinsic Field Action Recovery -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicFieldActionRecovery.Intrinsic

noncomputable section

/-! Recover the actual completion-field symplectic action from Gaussian
operator formulas after the given field isomorphism with the reals. -/

open OAI.RepresentationTheory.Weil.Local.FieldOscillator.Construction
open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicHeisenberg OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianActionRecovery.Intrinsic

theorem gaussian_action_parameter_character {n : ℕ} (ψ : AddChar ℝ ℂ)
    (hψ : ψ = Weil.Local.Gaussian.Construction.realCharacter 1) (W : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin n))
    (a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover ℝ n ψ) (φ : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (c : ℂ) (hc : c ≠ 0)
    (hzero : (Weil.AdelicSplitting.Oscillator.Construction.localOperator ℝ n ψ a φ).val = fun x => c * Weil.Local.SiegelGaussian.Construction.siegelGaussian W.matrix x)
    (q p : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) (η : Fin n → ℂ) (b : ℂ)
    (hshift : ∀ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator ℝ n ψ a (IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftedGaussianTest φ q p)).val x =
      b * IntrinsicGaussianUniqueness.IntrinsicHeisenberg.jacobiGaussian W.matrix η x) :
    let v := Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.AdelicSplitting.Oscillator.Construction.localProjection ℝ n ψ a) (Sum.elim q p)
    IntrinsicGaussianUniqueness.IntrinsicHeisenberg.realJacobi W.matrix (fun i => v (.inl i)) (fun i => v (.inr i)) = η := by
  subst ψ
  exact IntrinsicGaussianActionRecovery.Intrinsic.gaussian_action_parameter W a φ c hc hzero q p η b hshift

theorem field_gaussian_action_parameter
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (e : k ≃+* ℝ) (he : Continuous e) (hi : Continuous e.symm)
    (ψ : AddChar k ℂ) (hψ : Weil.Local.FieldFourier.Construction.fieldCharacter e ψ = Weil.Local.Gaussian.Construction.realCharacter 1)
    (a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k n ψ) (φ χ : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) (Z W : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin n))
    (q p : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) (η : Fin n → ℂ) (c b : ℂ) (hc : c ≠ 0)
    (hφ : ∀ x, φ.val (fun i => e.symm (x i)) = Weil.Local.SiegelGaussian.Construction.siegelGaussian Z.matrix x)
    (hχ : ∀ x, χ.val (fun i => e.symm (x i)) = IntrinsicGaussianUniqueness.IntrinsicHeisenberg.jacobiGaussian Z.matrix (IntrinsicGaussianUniqueness.IntrinsicHeisenberg.realJacobi Z.matrix q p) x)
    (hzero : ∀ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k n ψ a φ).val (fun i => e.symm (x i)) = c * Weil.Local.SiegelGaussian.Construction.siegelGaussian W.matrix x)
    (hact : ∀ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k n ψ a χ).val (fun i => e.symm (x i)) = b * IntrinsicGaussianUniqueness.IntrinsicHeisenberg.jacobiGaussian W.matrix η x) :
    let v := Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.FieldFourier.Construction.fieldSymplecticMap e n (Weil.AdelicSplitting.Oscillator.Construction.localProjection k n ψ a)) (Sum.elim q p)
    IntrinsicGaussianUniqueness.IntrinsicHeisenberg.realJacobi W.matrix (fun i => v (.inl i)) (fun i => v (.inr i)) = η := by
  let T := Weil.Local.FieldCoordinates.Construction.testSpaceTransport (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi n)
  let a' := Weil.Local.FieldOscillator.Construction.fieldOscillatorTransport e he hi n ψ a
  have ha (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) : Weil.AdelicSplitting.Oscillator.Construction.localOperator ℝ n (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) a' (T f) =
      T (Weil.AdelicSplitting.Oscillator.Construction.localOperator k n ψ a f) := Weil.Local.FieldOscillator.Construction.fieldOscillatorTransport_apply e he hi n ψ a f
  have hTφ : (T φ).val = Weil.Local.SiegelGaussian.Construction.siegelGaussian Z.matrix := funext hφ
  have hs : IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftedGaussianTest (T φ) q p = IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftFactor Z.matrix q p • T χ := by
    apply Subtype.ext
    funext x
    rw [IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shifted_gaussian_test_value Z.matrix Z.symmetric (T φ) hTφ]
    exact congrArg (fun t : ℂ => IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftFactor Z.matrix q p * t) (hχ x).symm
  have hz : (Weil.AdelicSplitting.Oscillator.Construction.localOperator ℝ n (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) a' (T φ)).val =
      fun x => c * Weil.Local.SiegelGaussian.Construction.siegelGaussian W.matrix x := by
    rw [ha]
    exact funext hzero
  have ht (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) :
      (Weil.AdelicSplitting.Oscillator.Construction.localOperator ℝ n (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) a' (IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftedGaussianTest (T φ) q p)).val x =
        (IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftFactor Z.matrix q p * b) * IntrinsicGaussianUniqueness.IntrinsicHeisenberg.jacobiGaussian W.matrix η x := by
    rw [hs,map_smul,ha]
    change IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftFactor Z.matrix q p *
      (Weil.AdelicSplitting.Oscillator.Construction.localOperator k n ψ a χ).val (fun i => e.symm (x i)) = _
    rw [hact,mul_assoc]
  exact gaussian_action_parameter_character (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) hψ W a' (T φ) c hc hz q p η
    (IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftFactor Z.matrix q p * b) ht

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicFieldActionRecovery.Intrinsic

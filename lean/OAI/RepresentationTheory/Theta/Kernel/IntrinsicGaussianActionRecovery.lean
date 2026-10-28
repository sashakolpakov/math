import OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianDisplacement
import OAI.RepresentationTheory.Weil.AdelicSplitting.Oscillator

/-! # Intrinsic Gaussian Action Recovery -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianActionRecovery.Intrinsic

noncomputable section

/-! Recover a real phase-space action from actual Gaussian operator
identities. The proof uses the defining Heisenberg intertwining, and
does not assume that candidate phase coordinates match the operator. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction
open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicHeisenberg OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicParameter OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianDisplacement.Intrinsic

theorem gaussian_action_parameter {n : ℕ} (W : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin n))
    (a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1)) (φ : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (c : ℂ) (hc : c ≠ 0)
    (hzero : (Weil.AdelicSplitting.Oscillator.Construction.localOperator ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a φ).val = fun x => c * Weil.Local.SiegelGaussian.Construction.siegelGaussian W.matrix x)
    (q p : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) (η : Fin n → ℂ) (b : ℂ)
    (hshift : ∀ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a (IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftedGaussianTest φ q p)).val x =
      b * IntrinsicGaussianUniqueness.IntrinsicHeisenberg.jacobiGaussian W.matrix η x) :
    let v := Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.AdelicSplitting.Oscillator.Construction.localProjection ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a) (Sum.elim q p)
    IntrinsicGaussianUniqueness.IntrinsicHeisenberg.realJacobi W.matrix (fun i => v (.inl i)) (fun i => v (.inr i)) = η := by
  dsimp only
  let v := Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.AdelicSplitting.Oscillator.Construction.localProjection ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a) (Sum.elim q p)
  let q' : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n := fun i => v (.inl i)
  let p' : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n := fun i => v (.inr i)
  have hv : v = Sum.elim q' p' := by funext i; cases i <;> rfl
  have ht := (a.property.2 (Sum.elim q p) φ (IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftedGaussianTest φ q p)).mp
    (show Weil.Local.FunctionsMetaplectic.Construction.heisenbergGraph (Weil.Local.Gaussian.Construction.realCharacter 1) (Sum.elim q p) φ (IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftedGaussianTest φ q p) from rfl)
  change (Weil.AdelicSplitting.Oscillator.Construction.localOperator ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a (IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftedGaussianTest φ q p)).val =
    Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction (Weil.Local.Gaussian.Construction.realCharacter 1) v (Weil.AdelicSplitting.Oscillator.Construction.localOperator ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a φ).val at ht
  rw [hzero] at ht
  have hs : IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftFactor W.matrix q' p' ≠ 0 := Complex.exp_ne_zero _
  apply IntrinsicGaussianUniqueness.IntrinsicParameter.scaled_jacobi_parameter_unique W.matrix _ η (c * IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftFactor W.matrix q' p') b
    (mul_ne_zero hc hs)
  intro x
  have he := congrFun ht x
  change _ = Weil.Local.Gaussian.Construction.realCharacter 1 (∑ i, v (.inr i) * (x i - v (.inl i) / 2)) *
    (c * Weil.Local.SiegelGaussian.Construction.siegelGaussian W.matrix (fun i => x i - v (.inl i))) at he
  rw [mul_left_comm] at he
  change _ = c * Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction (Weil.Local.Gaussian.Construction.realCharacter 1) v (Weil.Local.SiegelGaussian.Construction.siegelGaussian W.matrix) x at he
  rw [hv,IntrinsicGaussianUniqueness.IntrinsicHeisenberg.heisenberg_gaussian_formula W.matrix W.symmetric] at he
  exact (mul_assoc _ _ _).trans (he.symm.trans (hshift x))

theorem gaussian_action_displacement {n : ℕ} (W : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin n))
    (a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1)) (φ : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (c : ℂ) (hc : c ≠ 0)
    (hzero : (Weil.AdelicSplitting.Oscillator.Construction.localOperator ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a φ).val = fun x => c * Weil.Local.SiegelGaussian.Construction.siegelGaussian W.matrix x)
    (q p r s : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) (b : ℂ)
    (hshift : ∀ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a (IntrinsicGaussianUniqueness.IntrinsicHeisenberg.shiftedGaussianTest φ q p)).val x =
      b * IntrinsicGaussianUniqueness.IntrinsicHeisenberg.jacobiGaussian W.matrix (IntrinsicGaussianUniqueness.IntrinsicHeisenberg.realJacobi W.matrix r s) x) :
    Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.AdelicSplitting.Oscillator.Construction.localProjection ℝ n (Weil.Local.Gaussian.Construction.realCharacter 1) a) (Sum.elim q p) = Sum.elim r s := by
  have h := gaussian_action_parameter W a φ c hc hzero q p (IntrinsicGaussianUniqueness.IntrinsicHeisenberg.realJacobi W.matrix r s) b hshift
  obtain ⟨hr,hs⟩ := IntrinsicGaussianDisplacement.Intrinsic.real_jacobi_injective W _ _ r s h
  funext i
  cases i with
  | inl i => exact congrFun hr i
  | inr i => exact congrFun hs i

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianActionRecovery.Intrinsic

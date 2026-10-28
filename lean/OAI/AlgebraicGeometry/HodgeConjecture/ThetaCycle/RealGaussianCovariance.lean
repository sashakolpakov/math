import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.JacobiDisplacement
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.JacobiBlockAction

/-! # Real Gaussian Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCovariance.CM

noncomputable section

section

/-! ThetaCycle: exact real displacement coordinates, Jacobi change, and
exponential correction for the oscillator in classical graph order. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

def transformedPositionShift {N : ℕ} (g : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks (Fin N) ℝ)
    (q p : Fin N → ℝ) : Fin N → ℝ := g.D *ᵥ q + g.C *ᵥ p

def transformedMomentumShift {N : ℕ} (g : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks (Fin N) ℝ)
    (q p : Fin N → ℝ) : Fin N → ℝ := g.B *ᵥ q + g.A *ᵥ p

theorem transformed_position_complexification {N : ℕ} (g : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks (Fin N) ℝ)
    (q p : Fin N → ℝ) :
    (fun i => (transformedPositionShift g q p i : ℂ)) =
      g.complexify.D *ᵥ (fun i => (q i : ℂ)) + g.complexify.C *ᵥ (fun i => (p i : ℂ)) := by
  change (fun i => (((g.D *ᵥ q) i + (g.C *ᵥ p) i : ℝ) : ℂ)) = _
  simp only [Complex.ofReal_add]
  change (fun i => ((g.D *ᵥ q) i : ℂ)) + (fun i => ((g.C *ᵥ p) i : ℂ)) = _
  rw [RepresentationTheory.Weil.Local.SiegelGaussian.Construction.complexify_mulVec, RepresentationTheory.Weil.Local.SiegelGaussian.Construction.complexify_mulVec]
  rfl

theorem transformed_momentum_complexification {N : ℕ} (g : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks (Fin N) ℝ)
    (q p : Fin N → ℝ) :
    (fun i => (transformedMomentumShift g q p i : ℂ)) =
      g.complexify.B *ᵥ (fun i => (q i : ℂ)) + g.complexify.A *ᵥ (fun i => (p i : ℂ)) := by
  change (fun i => (((g.B *ᵥ q) i + (g.A *ᵥ p) i : ℝ) : ℂ)) = _
  simp only [Complex.ofReal_add]
  change (fun i => ((g.B *ᵥ q) i : ℂ)) + (fun i => ((g.A *ᵥ p) i : ℂ)) = _
  rw [RepresentationTheory.Weil.Local.SiegelGaussian.Construction.complexify_mulVec, RepresentationTheory.Weil.Local.SiegelGaussian.Construction.complexify_mulVec]
  rfl

theorem transformed_displacement_jacobi {N : ℕ} (g : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks (Fin N) ℝ)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (q p : Fin N → ℝ) :
    JacobiDisplacement.CM.displacementJacobi (g.transformSiegel Z) (transformedPositionShift g q p)
      (transformedMomentumShift g q p) = g.jacobiChange Z (JacobiDisplacement.CM.displacementJacobi Z q p) := by
  rw [JacobiDisplacement.CM.displacementJacobi, transformed_position_complexification, transformed_momentum_complexification,
    ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.transformSiegel_matrix, ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply]
  exact JacobiBlockAction.CM.jacobi_phase_action g.complexify Z.matrix Z.symmetric (g.denominator_det_isUnit Z) _ _

theorem transformed_displacement_pairing {N : ℕ} (g : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks (Fin N) ℝ)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (q p : Fin N → ℝ) :
    (fun i => (q i : ℂ)) ⬝ᵥ JacobiDisplacement.CM.displacementJacobi Z q p -
        (fun i => (transformedPositionShift g q p i : ℂ)) ⬝ᵥ
          JacobiDisplacement.CM.displacementJacobi (g.transformSiegel Z) (transformedPositionShift g q p)
            (transformedMomentumShift g q p) =
      -(JacobiDisplacement.CM.displacementJacobi Z q p ⬝ᵥ
        ((g.complexify.denominator Z.matrix)⁻¹ * g.complexify.C) *ᵥ JacobiDisplacement.CM.displacementJacobi Z q p) := by
  rw [transformed_displacement_jacobi, transformed_position_complexification,
    ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply]
  exact JacobiBlockAction.CM.jacobi_pairing_correction g.complexify Z.matrix (g.denominator_det_isUnit Z) _ _

theorem transformed_displacement_scalar {N : ℕ} (g : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks (Fin N) ℝ)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (q p : Fin N → ℝ) :
    JacobiDisplacement.CM.displacementScalar (g.transformSiegel Z) (transformedPositionShift g q p)
        (transformedMomentumShift g q p) / JacobiDisplacement.CM.displacementScalar Z q p =
      Complex.exp (-(g.thetaCorrectionForm Z (JacobiDisplacement.CM.displacementJacobi Z q p) (JacobiDisplacement.CM.displacementJacobi Z q p))) := by
  rw [JacobiDisplacement.CM.displacementScalar, JacobiDisplacement.CM.displacementScalar, ← Complex.exp_sub]
  congr 1
  calc
    _ = (Real.pi : ℂ) * Complex.I *
        ((fun i => (q i : ℂ)) ⬝ᵥ JacobiDisplacement.CM.displacementJacobi Z q p -
          (fun i => (transformedPositionShift g q p i : ℂ)) ⬝ᵥ
            JacobiDisplacement.CM.displacementJacobi (g.transformSiegel Z) (transformedPositionShift g q p)
              (transformedMomentumShift g q p)) := by ring
    _ = _ := by rw [transformed_displacement_pairing, ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.thetaCorrectionForm_apply, mul_neg]

theorem swapped_symplectic_phase_action {N : ℕ} (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℝ) (q p : Fin N → ℝ) :
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (OscillatorPhaseOrder.CM.swapSymplecticPhase g) (Sum.elim q p) =
      Sum.elim (transformedPositionShift (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g) q p) (transformedMomentumShift (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g) q p) := by
  change (OscillatorPhaseOrder.CM.swapSymplecticPhase g).val *ᵥ Sum.elim q p = _
  rw [OscillatorPhaseOrder.CM.swap_symplectic_phase_blocks]
  ext i
  cases i <;> simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks,
    transformedPositionShift, transformedMomentumShift, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks, Matrix.toBlocks₁₁,
    Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

end

/-! ThetaCycle: the full Jacobi-Gaussian transformation law of the actual real
oscillator. Its scalar is the independently computed coefficient at zero. -/

open scoped Classical _root_.Matrix

theorem displaced_gaussian_heisenberg_graph {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N))
    (q p : Fin N → ℝ) :
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergGraph (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (Sum.elim q p) (RealGaussianCoefficient.CM.realSiegelGaussian Z 0)
      (JacobiDisplacement.CM.displacementScalar Z q p • RealGaussianCoefficient.CM.realSiegelGaussian Z (JacobiDisplacement.CM.displacementJacobi Z q p)) := by
  funext x
  exact (JacobiDisplacement.CM.heisenberg_gaussian_displacement Z q p x).symm

theorem real_oscillator_displaced_gaussian {N : ℕ} (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℝ)
    (a : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1))
    (ha : RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a = OscillatorPhaseOrder.CM.swapSymplecticPhase g)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (q p : Fin N → ℝ) :
    a.val.2 (RealGaussianCoefficient.CM.realSiegelGaussian Z (JacobiDisplacement.CM.displacementJacobi Z q p)) =
      (RealGaussianCoefficient.CM.realGaussianCoefficient a Z *
          (JacobiDisplacement.CM.displacementScalar ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel Z)
              (transformedPositionShift (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g) q p) (transformedMomentumShift (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g) q p) /
            JacobiDisplacement.CM.displacementScalar Z q p)) •
        RealGaussianCoefficient.CM.realSiegelGaussian ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel Z)
          (JacobiDisplacement.CM.displacementJacobi ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel Z)
            (transformedPositionShift (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g) q p) (transformedMomentumShift (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g) q p)) := by
  obtain ⟨_, _, hcoeff⟩ := RealGaussianCoefficient.CM.real_oscillator_gaussian_coefficient g a ha
  have h := (a.property.2 (Sum.elim q p) (RealGaussianCoefficient.CM.realSiegelGaussian Z 0)
    (JacobiDisplacement.CM.displacementScalar Z q p • RealGaussianCoefficient.CM.realSiegelGaussian Z (JacobiDisplacement.CM.displacementJacobi Z q p))).mp
      (displaced_gaussian_heisenberg_graph Z q p)
  have hproj : a.val.1 = OscillatorPhaseOrder.CM.swapSymplecticPhase g := ha
  change (a.val.2 (JacobiDisplacement.CM.displacementScalar Z q p • RealGaussianCoefficient.CM.realSiegelGaussian Z (JacobiDisplacement.CM.displacementJacobi Z q p))).val =
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.symplecticAction a.val.1 (Sum.elim q p))
      (a.val.2 (RealGaussianCoefficient.CM.realSiegelGaussian Z 0)).val at h
  rw [hproj, swapped_symplectic_phase_action, (hcoeff Z).2, map_smul] at h
  apply Subtype.ext
  funext x
  have hx := congrFun h x
  have he : JacobiDisplacement.CM.displacementScalar Z q p *
        (a.val.2 (RealGaussianCoefficient.CM.realSiegelGaussian Z (JacobiDisplacement.CM.displacementJacobi Z q p))).val x =
      RealGaussianCoefficient.CM.realGaussianCoefficient a Z *
        (JacobiDisplacement.CM.displacementScalar ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel Z)
          (transformedPositionShift (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g) q p) (transformedMomentumShift (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g) q p) *
          (RealGaussianCoefficient.CM.realSiegelGaussian ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel Z)
            (JacobiDisplacement.CM.displacementJacobi ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel Z)
              (transformedPositionShift (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g) q p) (transformedMomentumShift (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g) q p))).val x) := by
    rw [← JacobiDisplacement.CM.heisenberg_gaussian_displacement]
    simpa only [RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      mul_assoc, mul_comm, mul_left_comm] using hx
  change (a.val.2 (RealGaussianCoefficient.CM.realSiegelGaussian Z (JacobiDisplacement.CM.displacementJacobi Z q p))).val x = _
  apply mul_left_cancel₀ (JacobiDisplacement.CM.displacement_scalar_ne_zero Z q p)
  rw [he]
  change _ = JacobiDisplacement.CM.displacementScalar Z q p *
    ((RealGaussianCoefficient.CM.realGaussianCoefficient a Z * (_ / JacobiDisplacement.CM.displacementScalar Z q p)) * _)
  field_simp [JacobiDisplacement.CM.displacement_scalar_ne_zero Z q p]

theorem real_oscillator_full_gaussian_covariance {N : ℕ} (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℝ)
    (a : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1))
    (ha : RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a = OscillatorPhaseOrder.CM.swapSymplecticPhase g)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) :
    a.val.2 (RealGaussianCoefficient.CM.realSiegelGaussian Z z) =
      (RealGaussianCoefficient.CM.realGaussianCoefficient a Z * Complex.exp (-(RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).thetaCorrectionForm Z z z)) •
        RealGaussianCoefficient.CM.realSiegelGaussian ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).transformSiegel Z) ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).jacobiChange Z z) := by
  obtain ⟨q, p, rfl⟩ := JacobiDisplacement.CM.exists_real_jacobi_displacement Z z
  have h := real_oscillator_displaced_gaussian g a ha Z q p
  rw [transformed_displacement_scalar, transformed_displacement_jacobi] at h
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCovariance.CM

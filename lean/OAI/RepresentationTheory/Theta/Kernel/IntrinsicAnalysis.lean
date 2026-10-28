import OAI.RepresentationTheory.Theta.Kernel.Analysis
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection

/-! # Intrinsic Analysis -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicAnalysis.Intrinsic

noncomputable section

/-! The full GaussianConvergence proposition gives Jacobi-variable smoothness for the
literal native theta kernel. Finite decompositions of the actual adelic
input then commute with the completed Taylor coefficients. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise ContDiff

open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K}
variable (B : Adelic.DataTheta.ComparisonData F H K A)

theorem completed_contDiff (hGaussianConvergence : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hTheta : Adelic.DataTheta.Descent.ThetaConstruction B) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A)) :
    ContDiff ℂ ⊤ (Adelic.DataTheta.completedTheta B f Z.matrix) := by
  obtain ⟨L, hL, φ, _, _, _, heq, _⟩ := hTheta.1 f
  let : DiscreteTopology L := hL
  have he : Adelic.DataTheta.completedTheta B f Z.matrix = Definitions.completedTheta L φ Z.matrix :=
    funext fun ξ => (heq Z ξ).2
  rw [he]
  unfold Definitions.completedTheta
  have hc : ContDiff ℂ ⊤ (AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor
      (((Real.pi : ℂ) / 2) • AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear ((AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z.matrix)⁻¹))) :=
    Complex.contDiff_exp.comp
      ((((Real.pi : ℂ) / 2) • AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear ((AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z.matrix)⁻¹)).contDiff.clm_apply
        contDiff_id)
  apply hc.mul
  rw [contDiff_iff_contDiffAt]
  exact fun ξ => (Analysis.lattice_analysis hGaussianConvergence L φ Z ξ).2

theorem completed_finite_sum (hTheta : Adelic.DataTheta.Descent.ThetaConstruction B)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m)) (n : ℕ) (factors : Fin n → Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (heval : ∀ x, Adelic.Evaluation.finiteSchwartzFunction F (3 * m) f x =
      ∑ j, Adelic.Evaluation.finiteSchwartzFunction F (3 * m) (factors j) x)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A)) :
    Adelic.DataTheta.completedTheta B f Z.matrix = fun ξ => ∑ j, Adelic.DataTheta.completedTheta B (factors j) Z.matrix ξ := by
  funext ξ
  have hsum : Adelic.DataTheta.rationalTheta B f Z.matrix ξ = ∑ j, Adelic.DataTheta.rationalTheta B (factors j) Z.matrix ξ := by
    simp only [Adelic.DataTheta.rationalTheta, Adelic.DataTheta.thetaSummand, Adelic.DataTheta.rationalWeight, heval, Finset.sum_mul]
    exact Summable.tsum_finsetSum (fun j _ => hTheta.2.1 (factors j) Z ξ)
  simp only [Adelic.DataTheta.completedTheta, hsum, Finset.mul_sum]

theorem completedTensor_finite_sum (hGaussianConvergence : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hTheta : Adelic.DataTheta.Descent.ThetaConstruction B)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m)) (n : ℕ) (factors : Fin n → Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (heval : ∀ x, Adelic.Evaluation.finiteSchwartzFunction F (3 * m) f x =
      ∑ j, Adelic.Evaluation.finiteSchwartzFunction F (3 * m) (factors j) x)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A)) (a : ℕ) :
    Adelic.DataTheta.completedTensor B f a Z.matrix = ∑ j, Adelic.DataTheta.completedTensor B (factors j) a Z.matrix := by
  unfold Adelic.DataTheta.completedTensor
  rw [completed_finite_sum B hTheta f n factors heval Z,
    iteratedFDeriv_fun_sum_apply (fun j _ =>
      ((completed_contDiff B hGaussianConvergence hTheta (factors j) Z).of_le (show (a : ℕ∞ω) ≤ ⊤ from le_top)).contDiffAt)]
  rw [Finset.smul_sum]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicAnalysis.Intrinsic

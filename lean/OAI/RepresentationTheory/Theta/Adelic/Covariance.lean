import OAI.RepresentationTheory.Theta.Adelic.LatticeIdentification
import OAI.RepresentationTheory.Theta.CompletionAnalysis

/-! # Covariance -/

namespace OAI.RepresentationTheory.Theta.Adelic.Covariance

noncomputable section

/-! Transfer completed-function and Taylor-tensor covariance through
the actual support-lattice identification. The pointwise theta law is
provided by the adelic Gaussian calculation. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.LatticeIdentification OAI.RepresentationTheory.Theta.Adelic.SupportLattice

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem completedTheta_covariance_of_theta
    (f fnew : FiniteSchwartz.finiteSchwartz F (3 * m)) (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks (BallGeometryData.FrameIndex A) ℝ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A)) (c : ℂ)
    (hp : ∀ ξ, DataTheta.rationalTheta (GeometricGaussians.constructedComparison A P) fnew (g.transformSiegel Z).matrix
      (g.jacobiChange Z ξ) = c * (Complex.exp (g.thetaCorrectionForm Z ξ ξ) *
        DataTheta.rationalTheta (GeometricGaussians.constructedComparison A P) f Z.matrix ξ)) (ξ : BallGeometryData.FrameIndex A → ℂ) :
    DataTheta.completedTheta (GeometricGaussians.constructedComparison A P) fnew (g.transformSiegel Z).matrix
      (g.jacobiChange Z ξ) = c * DataTheta.completedTheta (GeometricGaussians.constructedComparison A P) f Z.matrix ξ := by
  rw [LatticeIdentification.completedTheta_lattice, LatticeIdentification.completedTheta_lattice]
  apply CompletionAnalysis.completedTheta_covariance
  intro η
  rw [← LatticeIdentification.rationalTheta_lattice A P, ← LatticeIdentification.rationalTheta_lattice A P]
  exact hp η

theorem completedTensor_covariance_of_theta
    (f fnew : FiniteSchwartz.finiteSchwartz F (3 * m)) (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks (BallGeometryData.FrameIndex A) ℝ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A)) (c : ℂ)
    (hp : ∀ ξ, DataTheta.rationalTheta (GeometricGaussians.constructedComparison A P) fnew (g.transformSiegel Z).matrix
      (g.jacobiChange Z ξ) = c * (Complex.exp (g.thetaCorrectionForm Z ξ ξ) *
        DataTheta.rationalTheta (GeometricGaussians.constructedComparison A P) f Z.matrix ξ))
    (a : ℕ) (v : Fin a → BallGeometryData.FrameIndex A → ℂ) :
    DataTheta.completedTensor (GeometricGaussians.constructedComparison A P) fnew a (g.transformSiegel Z).matrix
      (fun i => g.jacobiChange Z (v i)) =
        c * DataTheta.completedTensor (GeometricGaussians.constructedComparison A P) f a Z.matrix v := by
  rw [LatticeIdentification.completedTensor_lattice, LatticeIdentification.completedTensor_lattice]
  apply CompletionAnalysis.completedTensor_covariance
  intro η
  rw [← LatticeIdentification.rationalTheta_lattice A P, ← LatticeIdentification.rationalTheta_lattice A P]
  exact hp η

end

end OAI.RepresentationTheory.Theta.Adelic.Covariance

import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.BasisTransport
import OAI.RepresentationTheory.Theta.Adelic.DataTheta
import OAI.RepresentationTheory.Theta.Geometric.LinearTheta

/-! # Transported Theta -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TransportedTheta.TestTransport

noncomputable section

/-! The transported finite test has the same literal rational theta
series and the same first completed coefficient in the retained basis. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.TotallyRealData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Geometric.LinearTheta

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H K}
variable (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A)

theorem transportedThetaSummand (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) (z : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) (x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) :
    RepresentationTheory.Theta.Adelic.DataTheta.thetaSummand B (Finite.BasisTransport.Test.transportBasisTest A B.rationalPosition φ) Z.matrix z x =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm φ Z z (B.rationalPosition x) := by
  unfold RepresentationTheory.Theta.Adelic.DataTheta.thetaSummand RepresentationTheory.Theta.Adelic.DataTheta.rationalWeight
  rw [show (fun i => algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (x i)) = RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x from rfl,
    Finite.BasisTransport.Test.transportBasisTest_rational_value]
  simp only [RepresentationTheory.Theta.Adelic.DataTheta.gaussianValue, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm, Complex.ofReal_ratCast]

theorem transportedRationalTheta (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) (z : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta B (Finite.BasisTransport.Test.transportBasisTest A B.rationalPosition φ) Z.matrix z =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta φ Z z := by
  unfold RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta
  simp only [transportedThetaSummand]
  exact B.rationalPosition.toEquiv.tsum_eq (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm φ Z z)

theorem transportedCompleted_hasFDerivAt (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) :
    HasFDerivAt (RepresentationTheory.Theta.Adelic.DataTheta.completedTheta B (Finite.BasisTransport.Test.transportBasisTest A B.rationalPosition φ) Z.matrix)
      (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst φ Z) 0 := by
  have hraw := funext (transportedRationalTheta B φ Z)
  unfold RepresentationTheory.Theta.Adelic.DataTheta.completedTheta
  rw [hraw]
  exact ComplexMultiplication.ThetaCompletion.CM.thetaCompletion_mul_hasFDerivAt_zero _ (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst_hasFDerivAt φ Z)

theorem transportedCompleted_first (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) (u : Fin 1 → RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.completedTensor B (Finite.BasisTransport.Test.transportBasisTest A B.rationalPosition φ) 1 Z.matrix u =
      RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst φ Z (u 0) := by
  simp only [RepresentationTheory.Theta.Adelic.DataTheta.completedTensor, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    iteratedFDeriv_one_apply, (transportedCompleted_hasFDerivAt B φ Z).fderiv]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TransportedTheta.TestTransport

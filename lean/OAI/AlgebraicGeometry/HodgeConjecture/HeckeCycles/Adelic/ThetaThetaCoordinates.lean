import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.RationalPositionCoordinates
import OAI.RepresentationTheory.Theta.Adelic.DataTheta
import OAI.RepresentationTheory.Theta.Geometric.LinearTheta

/-! # Theta Theta Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaThetaCoordinates.CM

noncomputable section

/-! AdelicTheta's literal rational theta sum is PoissonAutomorphy's theta sum in the actual
rational position frame. The input maps transport genuine finite Schwartz
functions and retain arbitrary original restricted-tensor inputs. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation

variable (F : Type) [Field F] [NumberField F] {a : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a))ˣ}
  {K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a))ˣ}
  {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F a m H K} (T : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A)

def toRational : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m) →ₗ[ℂ]
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) :=
  (Finite.RationalPositionCoordinates.CM.equivalence F (3 * m) T.rationalPosition).symm.toLinearMap.comp
    (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F (3 * m))

def sectionMap : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) →ₗ[ℂ]
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m) :=
  Finite.RationalPositionCoordinates.CM.tensorSection F (3 * m) T.rationalPosition

theorem rational_weight (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (x : Fin (3 * m) → F) :
    RepresentationTheory.Theta.Adelic.DataTheta.rationalWeight f x = (toRational F T f).val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (T.rationalPosition x)) :=
  (Finite.RationalPositionCoordinates.CM.inverse_rational_value F (3 * m) T.rationalPosition
    (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F (3 * m) f) x).symm

theorem section_rational (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) :
    toRational F T (sectionMap F T φ) = φ := by
  apply (Finite.RationalPositionCoordinates.CM.equivalence F (3 * m) T.rationalPosition).injective
  change (Finite.RationalPositionCoordinates.CM.equivalence F (3 * m) T.rationalPosition)
    ((Finite.RationalPositionCoordinates.CM.equivalence F (3 * m) T.rationalPosition).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  funext x
  exact Finite.RationalPositionCoordinates.CM.tensor_value F (3 * m) T.rationalPosition φ x

theorem theta_eq (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) (z : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T f Z.matrix z = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta (toRational F T f) Z z := by
  calc
    _ = ∑' x : Fin (3 * m) → F, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm (toRational F T f) Z z (T.rationalPosition x) := by
      apply tsum_congr
      intro x
      unfold RepresentationTheory.Theta.Adelic.DataTheta.thetaSummand
      rw [rational_weight F T]
      simp only [RepresentationTheory.Theta.Adelic.DataTheta.gaussianValue, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm, Complex.ofReal_ratCast]
    _ = _ := T.rationalPosition.toEquiv.tsum_eq _

theorem section_theta (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) (z : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T (sectionMap F T φ) Z.matrix z = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta φ Z z := by
  rw [theta_eq, section_rational]

theorem first_derivative (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) :
    fderiv ℂ (RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T f Z.matrix) 0 = RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst (toRational F T f) Z := by
  have he : RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T f Z.matrix = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta (toRational F T f) Z :=
    funext (theta_eq F T f Z)
  rw [he]
  exact (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst_hasFDerivAt (toRational F T f) Z).fderiv

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaThetaCoordinates.CM

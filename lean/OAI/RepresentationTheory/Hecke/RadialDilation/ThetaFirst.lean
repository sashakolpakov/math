import OAI.RepresentationTheory.Hecke.RadialDilation.Cm
import OAI.RepresentationTheory.Theta.Geometric.LinearTheta

/-! # Theta First -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.ThetaFirst.Realization

noncomputable section

/-!
# Actual finite-adelic first-derivative covariance for RadialDilation

This uses GeometricTheta's proved identity between the rational theta series and its
first coefficient. The only automorphy input is the repaired PoissonAutomorphy proposition;
neither lattice reindexing nor a derivative identity is assumed here.
-/

open OAI.RepresentationTheory.Theta.Geometric.LinearTheta

universe ui ur uf ua

variable {ι : Type ui} [Fintype ι] [DecidableEq ι]
variable {MpR : Type ur} {MpF : Type uf} {MpA : Type ua}
  [Group MpR] [Group MpF] [Group MpA]

theorem actual_first_theta_covariance
    (hPoissonAutomorphy : Prerequisites.Core.PoissonAutomorphy.Proposition.{ui, ur, uf, ua})
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) (γ : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ)
    (Φ : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    (Theta.Geometric.LinearTheta.canonicalFirst (D.finiteAction γ Φ) ((Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z)).comp
        ((Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z) =
      Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z • Theta.Geometric.LinearTheta.canonicalFirst Φ Z := by
  have h := hPoissonAutomorphy ι MpR MpF MpA D γ
  exact AlgebraicGeometry.ComplexMultiplication.ThetaCovariance.CM.theta_first_derivative_covariance
    ((Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z) ((Theta.PoissonAutomorphyNormalizationData.realBlocks γ).thetaCorrectionForm Z)
    (Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z)
    (Theta.Geometric.LinearTheta.canonicalFirst_hasFDerivAt Φ Z)
    (Theta.Geometric.LinearTheta.canonicalFirst_hasFDerivAt (D.finiteAction γ Φ) ((Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z))
    (h.2.2.2.2 Φ Z)

end

end OAI.RepresentationTheory.Hecke.RadialDilation.ThetaFirst.Realization

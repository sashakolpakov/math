import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ConnectionEnergyBlocks
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionCoefficientComplex
import OAI.AlgebraicGeometry.DivisorClass.Chern.GradientCoefficientComplex
import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionMatrixComplex

/-! # Connection Coefficient Complex -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The actual projective principal and connection coefficients commute with complex scalars in the original normalized Hilbert coordinates. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem Projective.ConnectionCoefficientComplex.projectivePhysicalGradientScale_complex_smul (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (r : ℂ) (v : GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :
    Projective.ConnectionEnergyBlocks.projectivePhysicalGradientScale V n (r • v) = r • Projective.ConnectionEnergyBlocks.projectivePhysicalGradientScale V n v :=
  smul_comm (2 * Real.pi * Complex.I : ℂ) r v

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ) (i : V.analyticSpace)
  (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineGradientCoefficient_complex_smul
    (r : ℂ) (v : GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :
    h.projectiveLineGradientCoefficient V e n i z (r • v) = r • h.projectiveLineGradientCoefficient V e n i z v :=
  GradientCoefficientComplex.covectorGradientCoefficient_complex_smul _ n _ _ r v

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineSobolevCoefficient_complex_smul
    (r : ℂ) (v : GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :
    h.projectiveLineSobolevCoefficient V e n i z (r • v) = r • h.projectiveLineSobolevCoefficient V e n i z v :=
  ConnectionMatrixComplex.complexScaleCoefficient_complex_smul _ _ (h.projectiveLineGradientCoefficient_complex_smul V e n i z) r v

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineConnectionCoefficient_complex_smul
    (r : ℂ) (v : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :
    h.projectiveLineConnectionCoefficient V e n i z (r • v) = r • h.projectiveLineConnectionCoefficient V e n i z v :=
  Line.ConnectionCoefficientComplex.lineGradientConnectionCoefficient_complex_smul _ n _ _ r v

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineValueGradientCoefficient_complex_smul
    (r : ℂ) (v : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :
    h.projectiveLineValueGradientCoefficient V e n i z (r • v) = r • h.projectiveLineValueGradientCoefficient V e n i z v :=
  ConnectionMatrixComplex.connectionValueGradientMatrix_complex_smul _ _ _ (h.projectiveLineGradientCoefficient_complex_smul V e n i z)
    (Projective.ConnectionCoefficientComplex.projectivePhysicalGradientScale_complex_smul V n) (h.projectiveLineConnectionCoefficient_complex_smul V e n i z) r v

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineGradientValueCoefficient_complex_smul
    (r : ℂ) (v : GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :
    h.projectiveLineGradientValueCoefficient V e n i z (r • v) = r • h.projectiveLineGradientValueCoefficient V e n i z v :=
  ConnectionMatrixComplex.connectionGradientValueMatrix_complex_smul _ _ _ (h.projectiveLineGradientCoefficient_complex_smul V e n i z)
    (Projective.ConnectionCoefficientComplex.projectivePhysicalGradientScale_complex_smul V n) (h.projectiveLineConnectionCoefficient_complex_smul V e n i z) r v

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineConnectionValueCoefficient_complex_smul
    (r : ℂ) (v : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :
    h.projectiveLineConnectionValueCoefficient V e n i z (r • v) = r • h.projectiveLineConnectionValueCoefficient V e n i z v :=
  ConnectionMatrixComplex.connectionValueMatrix_complex_smul _ _ (h.projectiveLineGradientCoefficient_complex_smul V e n i z)
    (h.projectiveLineConnectionCoefficient_complex_smul V e n i z) r v

end

end OAI.AlgebraicGeometry.DivisorClass.Chern

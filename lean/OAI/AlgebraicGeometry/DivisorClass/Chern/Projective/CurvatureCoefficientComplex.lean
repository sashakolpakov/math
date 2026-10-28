import OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorCoefficientComplex
import OAI.AlgebraicGeometry.DivisorClass.Chern.CurvatureComplex
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ConnectionCoefficientComplex
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveBochner.WeakMatrix
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.WeightedSchwartzTests

/-! # Curvature Coefficient Complex -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original full curvature, complete value coefficient, and weighted forcing coefficient preserve complex scalars without changing their projection or adjoint order. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFullCurvatureOperator_complex_smul
    (r : ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1) :
    h.projectiveFullCurvatureOperator V e z (r • a) = r • h.projectiveFullCurvatureOperator V e z a :=
  CurvatureComplex.fullBochnerCurvatureCLM_complex_smul _ _ _ _ _ r a

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLinePairCoefficient_complex_smul
    (n : ℕ) (i : V.analyticSpace) (r : ℂ) (a : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :
    h.projectiveLinePairCoefficient V e n i z (r • a) = r • h.projectiveLinePairCoefficient V e n i z a :=
  CovectorCoefficientComplex.covectorPairCoefficient_complex_smul _ n _ _ r a

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineWeakCurvatureCoefficient_complex_smul
    (i : V.analyticSpace) (r : ℂ) (a : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) :
    h.projectiveLineWeakCurvatureCoefficient V e i z (r • a) = r • h.projectiveLineWeakCurvatureCoefficient V e i z a := by
  have hL (c : ℂ) (v : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1) :
      ((h.projectiveFullCurvatureOperator V e z).comp OneCovectorAntiProjection.oneCovectorAntiProjection) (c • v) =
      c • ((h.projectiveFullCurvatureOperator V e z).comp OneCovectorAntiProjection.oneCovectorAntiProjection) v := by
    change h.projectiveFullCurvatureOperator V e z (OneCovectorAntiProjection.oneCovectorAntiProjection (c • v)) =
      c • h.projectiveFullCurvatureOperator V e z (OneCovectorAntiProjection.oneCovectorAntiProjection v)
    rw [OneCovectorAntiProjection.oneCovectorAntiProjection_complex_smul, h.projectiveFullCurvatureOperator_complex_smul V e z]
  exact CovectorCoefficientComplex.covectorWeakActionCoefficient_complex_smul _ 1 _ _ _ hL r a

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineWeakValueCoefficient_complex_smul
    (i : V.analyticSpace) (r : ℂ) (a : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) :
    h.projectiveLineWeakValueCoefficient V e i z (r • a) = r • h.projectiveLineWeakValueCoefficient V e i z a := by
  change (h.projectiveLineConnectionValueCoefficient V e 1 i z + h.projectiveLineWeakCurvatureCoefficient V e i z) (r • a) =
    r • (h.projectiveLineConnectionValueCoefficient V e 1 i z + h.projectiveLineWeakCurvatureCoefficient V e i z) a
  rw [_root_.add_apply, _root_.add_apply, h.projectiveLineConnectionValueCoefficient_complex_smul V e 1 i z,
    h.projectiveLineWeakCurvatureCoefficient_complex_smul V e z i, smul_add]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedAntiTestCoefficient_complex_smul
    (i : V.analyticSpace) (r : ℂ) (a : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) :
    h.projectiveWeightedAntiTestCoefficient V e i z (r • a) = r • h.projectiveWeightedAntiTestCoefficient V e i z a := by
  let P := CovectorPairCoefficient.covectorOperatorCoordinates (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 OneCovectorAntiProjection.oneCovectorAntiProjection
  have hP : ∀ (c : ℂ) (v : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1), P (c • v) = c • P v :=
    CovectorCoefficientComplex.covectorOperatorCoordinates_complex_smul _ 1 _ OneCovectorAntiProjection.oneCovectorAntiProjection_complex_smul
  change (h.projectiveLinePairCoefficient V e 1 i z).adjoint (P (r • a)) =
    r • (h.projectiveLinePairCoefficient V e 1 i z).adjoint (P a)
  rw [hP, Analysis.HodgeTheory.Decomposition.ComplexOperatorLift.Constructions.real_adjoint_complex_smul (h.projectiveLinePairCoefficient V e 1 i z)
    (h.projectiveLinePairCoefficient_complex_smul V e z 1 i)]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern

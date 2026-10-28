import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.RescalePair
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Potential
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.GlobalPairCoordinates

/-! # Potential Chart Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Exact original chart densities after multiplication by an actual scalar metric potential. -/

open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.withPotential_globalFormPair_re
    (φ : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) (n : ℕ)
    (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (x : V.analyticSpace) :
    ((h.withPotential φ).globalFormPair V n a b x).re =
      Real.exp (ScalarPotentialFunctions.realPotentialScalar φ x) * (h.globalFormPair V n a b x).re :=
  h.rescale_globalFormPair_re V _ _ _ n a b x

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.withPotential_projectiveGlobalPair_re
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (φ : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) (n : ℕ)
    (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    ((h.withPotential φ).projectiveGlobalPair V e n a b z).re =
      Real.exp (ScalarPotentialFunctions.realPotentialScalar φ (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)) *
        (h.projectiveGlobalPair V e n a b z).re := by
  simp only [HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveGlobalPair, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [h.withPotential_globalFormPair_re V φ n a b]
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern

import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.TensorSmooth
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.FrameScalarGlue
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RoughEnergyDensity

/-! # Glued Divergence -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! Native tensor energy and flux glued across all original line frames in each fixed base chart. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveTensorPair (U : Opens V.analyticSpace) (n : ℕ)
    (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ :=
  Projective.FrameScalarGlue.projectiveLineScalarGlue V e (h.projectiveFrameTensorPair V e U n a c)

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveTensorFlux (U : Opens V.analyticSpace) (n : ℕ)
    (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) (k : Fin (Module.finrank ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
    ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ :=
  Projective.FrameScalarGlue.projectiveLineScalarGlue V e (fun i => h.projectiveFrameTensorFlux V e U n a c i k)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveTensorPair_onOpen
    (U : Opens V.analyticSpace) (n : ℕ) (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    (i : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e
      (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    h.projectiveTensorPair V e U n a c z = h.projectiveFrameTensorPair V e U n a c i z :=
  Projective.FrameScalarGlue.projectiveLineScalarGlue_onOpen V u e U (h.projectiveFrameTensorPair V e U n a c)
    (fun i j _ hz => h.projectiveFrameTensorPair_transition V e he U n a c i j hz) i hz

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveTensorFlux_onOpen
    (U : Opens V.analyticSpace) (n : ℕ) (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    (i : V.analyticSpace) (k : Fin (Module.finrank ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e
      (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    h.projectiveTensorFlux V e U n a c k z = h.projectiveFrameTensorFlux V e U n a c i k z :=
  Projective.FrameScalarGlue.projectiveLineScalarGlue_onOpen V u e U (fun i => h.projectiveFrameTensorFlux V e U n a c i k)
    (fun i j _ hz => h.projectiveFrameTensorFlux_transition V e he U n a c i j k hz) i hz

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveTensorPair_smooth
    (U : Opens V.analyticSpace) (n : ℕ) (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) :
    ContDiffOn ℝ ∞ (h.projectiveTensorPair V e U n a c) (ConnectionChartDerivative.projectiveOpenChartDomain V e U : Set _) :=
  Projective.FrameScalarGlue.projectiveLineScalarGlue_smooth V u e U (h.projectiveFrameTensorPair V e U n a c)
    (fun i j _ hz => h.projectiveFrameTensorPair_transition V e he U n a c i j hz)
    (h.projectiveFrameTensorPair_smooth V e he U n a c)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveTensorFlux_smooth
    (U : Opens V.analyticSpace) (n : ℕ) (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    (k : Fin (Module.finrank ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
    ContDiffOn ℝ ∞ (h.projectiveTensorFlux V e U n a c k) (ConnectionChartDerivative.projectiveOpenChartDomain V e U : Set _) :=
  Projective.FrameScalarGlue.projectiveLineScalarGlue_smooth V u e U (fun i => h.projectiveFrameTensorFlux V e U n a c i k)
    (fun i j _ hz => h.projectiveFrameTensorFlux_transition V e he U n a c i j k hz)
    (fun i => h.projectiveFrameTensorFlux_smooth V e he U n a c i k)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveTensorPair_self_nonneg
    (U : Opens V.analyticSpace) (n : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e U) :
    0 ≤ (h.projectiveTensorPair V e U n a a z).re := by
  let i := e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)
  have hzi : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :=
    ⟨hz.1, (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain i⟩
  rw [h.projectiveTensorPair_onOpen V e he U n a a i ⟨hz.1, hz.2, hzi.2⟩]
  simpa only [HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFrameTensorPair, CovectorTensorAlgebra.covectorTensorMetricPair, Line.RoughAnti.lineCovectorAntiDerivative, mul_assoc] using
    h.projectiveRoughEnergyDensity_nonneg V e he n i (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension) hzi

end

/-! The derivative of the glued original flux equals the native rough operator pairing and tensor energy. -/

open Filter _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFrameRoughPair (U : Opens V.analyticSpace) (n : ℕ)
    (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) (i : V.analyticSpace) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
  (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z : ℂ) * (h.projectiveWeightChart V e i z *
    Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
      (Line.RoughAnti.lineCovectorRoughLaplacian (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
        (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension) z)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (c.val i).extension z))

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveRoughPair (U : Opens V.analyticSpace) (n : ℕ)
    (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ :=
  Projective.FrameScalarGlue.projectiveLineScalarGlue V e (h.projectiveFrameRoughPair V e U n a c)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveTensorFlux_fderiv_onOpen
    (U : Opens V.analyticSpace) (n : ℕ) (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    (i : V.analyticSpace) (k : Fin (Module.finrank ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e
      (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    fderiv ℝ (h.projectiveTensorFlux V e U n a c k) z =
      fderiv ℝ (h.projectiveFrameTensorFlux V e U n a c i k) z := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [(ConnectionChartDerivative.projectiveOpenChartDomain V e _).isOpen.mem_nhds hz] with y hy
  exact h.projectiveTensorFlux_onOpen V e he U n a c i k hy

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveTensorFlux_divergence_frame
    (U : Opens V.analyticSpace) (n : ℕ) (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    (i : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e
      (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    (∑ k, fderiv ℝ (h.projectiveTensorFlux V e U n a c k) z
        ((stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) k)) =
      -h.projectiveFrameRoughPair V e U n a c i z + h.projectiveFrameTensorPair V e U n a c i z := by
  simp_rw [h.projectiveTensorFlux_fderiv_onOpen V e he U n a c i _ hz]
  have hd := h.projectiveRoughDivergence V e he n U a c i hz
  dsimp only at hd
  simp only [mul_add, mul_neg, mul_assoc] at hd
  exact hd

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveTensorFlux_divergence
    (U : Opens V.analyticSpace) (n : ℕ) (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e U) :
    (∑ k, fderiv ℝ (h.projectiveTensorFlux V e U n a c k) z
        ((stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) k)) =
      -h.projectiveRoughPair V e U n a c z + h.projectiveTensorPair V e U n a c z := by
  let i := e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)
  have hzi : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e
      (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :=
    ⟨hz.1, hz.2, (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain i⟩
  rw [h.projectiveTensorPair_onOpen V e he U n a c i hzi]
  exact h.projectiveTensorFlux_divergence_frame V e he U n a c i hzi

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveRoughPair_onOpen
    (U : Opens V.analyticSpace) (n : ℕ) (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    (i : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e
      (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    h.projectiveRoughPair V e U n a c z = h.projectiveFrameRoughPair V e U n a c i z := by
  have hg := h.projectiveTensorFlux_divergence V e he U n a c ⟨hz.1, hz.2.1⟩
  have hi := h.projectiveTensorFlux_divergence_frame V e he U n a c i hz
  rw [h.projectiveTensorPair_onOpen V e he U n a c i hz] at hg
  exact neg_injective (add_right_cancel (hg.symm.trans hi))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern

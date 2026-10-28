import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ProjectedOneAdjoint
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AdjointFrameCovector
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.OneCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.AntiTwoContractions

/-! # One Adjoint Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! The native degree-one covariant adjoint and Kähler formula use the projected original global Dolbeault adjoint. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (i : V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectedDegreeCodifferentialOne_covector
    (b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 2) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1
      ((Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I (h.degreeCodifferential V 1 b.val)).val i).extension z =
      Line.ConnectionSymbols.lineCovariantCodifferential (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
        (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 (b.val.val i).extension) z := by
  let W : Opens V.analyticSpace := Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i
  let x := Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z
  have hx : x ∈ W := ⟨e.map_target hz.1, hz.2⟩
  obtain ⟨f, hf, hs, hfx⟩ := Analysis.HodgeTheory.Decomposition.AdjointLocality.Constructions.exists_projective_cutoff_at V W.isOpen x hx
  let P := Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I (h.degreeCodifferential V 1 b.val)
  have hr : Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1
      ((Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 1 (fun y => star (f y)) (Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.conjugateFunction_smooth V f hf) P).val i).extension z =
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (P.val i).extension z := by
    unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm
    rw [Holomorphic.AntiMultiplication.holomorphicLineSmoothMul_inChart u ⊤ _ _ 1 P i e ⟨trivial, hz.2⟩]
    change (star (f x) • (P.val i).extension.inChart e (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)).compContinuousLinearMap _ = _
    rw [hfx, star_one, one_smul]
  have hc := congrArg (fun a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1 => Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension z)
    (h.weightedCovariantAdjointOne_projected_eq_global V e he i f hf hs b)
  change Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1
    (Manifold.OneFormProjection.openManifoldOnePart Complex.I ((h.weightedCovariantChartAdjoint V e he i 1 f hf hs b.val).val i)).extension z = _ at hc
  rw [hr, Projective.OneCoordinates.projectiveOpenChartForm_onePart V e he
      (⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) Complex.I
      ((h.weightedCovariantChartAdjoint V e he i 1 f hf hs b.val).val i) ⟨hz.1, trivial, hz.2⟩,
    h.weightedCovariantChartAdjoint_covector V e he i 1 f hf hs b.val hz, hfx, star_one, one_smul,
    h.chartCovariantAdjointFrame_covector V e he i 1 b.val hz,
    Projective.OneCoordinates.oneCovectorPart_eq_of_anti _ (h.projectiveCovariantAdjointOne_anti V e he ⊤ b i ⟨hz.1, trivial, hz.2⟩)] at hc
  exact hc.symm

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveKahler_globalDolbeaultAdjointOne
    (b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 2) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions.metricLefschetzContraction 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
        (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
        (Line.ConnectionSymbols.lineTwistedExteriorDerivative 2 (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
          (h.projectiveConnectionChart V e i) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 (b.val.val i).extension) z) -
      Line.ConnectionSymbols.lineTwistedExteriorDerivative 0 (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) (h.projectiveConnectionChart V e i)
        (fun y => Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions.metricLefschetzContraction 0 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e y)
          (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 (b.val.val i).extension y)) z =
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1
        ((Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I (h.degreeCodifferential V 1 b.val)).val i).extension z :=
  (h.projectiveKahler V e he 0 ⊤ b.val i ⟨hz.1, trivial, hz.2⟩).trans
    (h.projectedDegreeCodifferentialOne_covector V e he i b hz).symm

end

/-! The smooth degree-one Laplacian of the original bundle Dolbeault complex and its actual metric energy identity. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

def HolomorphicMetric.Data.HolomorphicLineMetricData.smoothDolbeaultLaplacianOne
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1 :=
  (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ (h.degreeCodifferential V 0 a.val))).val +
    Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I (h.degreeCodifferential V 1 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothDolbeaultLaplacianOne_anti
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    h.smoothDolbeaultLaplacianOne V a ∈ HolomorphicLine.AntiForms.holomorphicLineAntiFormSubmodule u ⊤ 1 :=
  (HolomorphicLine.AntiForms.holomorphicLineAntiFormSubmodule u ⊤ 1).add_mem
    (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ (h.degreeCodifferential V 0 a.val))).property
    (Holomorphic.OneFormProjection.holomorphicLineOnePart_anti u ⊤ _)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothDolbeaultLaplacianOne_pair
    (a b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    h.formIntegralPair V 1 (h.smoothDolbeaultLaplacianOne V a) b.val =
      h.formIntegralPair V 0 (h.degreeCodifferential V 0 a.val) (h.degreeCodifferential V 0 b.val) +
      h.formIntegralPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 b).val := by
  let f := h.degreeCodifferential V 0 a.val
  let da := (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val
  let first := (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ f)).val
  let second := Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I (h.degreeCodifferential V 1 da)
  have hfirst : h.formIntegralPair V 1 first b.val =
      h.formIntegralPair V 0 f (h.degreeCodifferential V 0 b.val) :=
    h.degreeCodifferential_pair_right V 0 (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ f) b.val
  have hsecond : h.formIntegralPair V 1 second b.val =
      h.formIntegralPair V 2 da (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 b).val := by
    have hp := h.onePart_integral_pair V (h.degreeCodifferential V 1 da) b.val
    rw [Holomorphic.OneFormProjection.holomorphicLineOnePart_eq_of_anti u ⊤ b.val b.property] at hp
    exact hp.trans (h.degreeCodifferential_pair V 1 b da).symm
  exact (h.formIntegralPair_add_left V 1 first second b.val).trans (congrArg₂ (fun x y : ℂ => x + y) hfirst hsecond)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothDolbeaultLaplacianOne_nonneg
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    0 ≤ (h.formIntegralPair V 1 (h.smoothDolbeaultLaplacianOne V a) a.val).re := by
  rw [h.smoothDolbeaultLaplacianOne_pair, Complex.add_re]
  exact add_nonneg (h.formIntegralPair_nonneg V 0 _) (h.formIntegralPair_nonneg V 2 _)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothDolbeaultLaplacianOne_kernel
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (hz : h.smoothDolbeaultLaplacianOne V a = 0) :
    h.degreeCodifferential V 0 a.val = 0 ∧ HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a = 0 := by
  have he := h.smoothDolbeaultLaplacianOne_pair V a a
  have he0 : (h.formIntegralPair V 1 (h.smoothDolbeaultLaplacianOne V a) a.val).re = 0 := by
    rw [hz]
    have hzero := h.formIntegralPair_smul_left V 1 a.val a.val 0
    rw [zero_smul, map_zero, zero_mul] at hzero
    exact congrArg Complex.re hzero
  have hsum : (h.formIntegralPair V 0 (h.degreeCodifferential V 0 a.val) (h.degreeCodifferential V 0 a.val)).re +
      (h.formIntegralPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val).re = 0 :=
    (Complex.add_re _ _).symm.trans ((congrArg Complex.re he).symm.trans he0)
  have h0 := h.formIntegralPair_nonneg V 0 (h.degreeCodifferential V 0 a.val)
  have h1 := h.formIntegralPair_nonneg V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val
  refine ⟨h.formIntegralPair_definite V 0 _ (by linarith), ?_⟩
  apply Subtype.ext
  exact h.formIntegralPair_definite V 2 _ (by linarith)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothDolbeaultLaplacianOne_of_closed_coclosed
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (h0 : h.degreeCodifferential V 0 a.val = 0)
    (h1 : HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a = 0) : h.smoothDolbeaultLaplacianOne V a = 0 := by
  have hf0 : HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ (h.degreeCodifferential V 0 a.val) = 0 :=
    (congrArg (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤) h0).trans (map_zero (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤))
  have hf1 := (congrArg (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0) hf0).trans (map_zero (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0))
  have hf : (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ (h.degreeCodifferential V 0 a.val))).val = 0 :=
    congrArg (fun a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 => a.val) hf1
  have hd0 : h.degreeCodifferential V 1 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val = 0 :=
    (congrArg (h.degreeCodifferential V 1) (congrArg (fun a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 2 => a.val) h1)).trans
      (map_zero (h.degreeCodifferential V 1))
  have hd := (congrArg (Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I) hd0).trans (map_zero (Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I))
  exact (congrArg₂ (fun x y : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1 => x + y) hf hd).trans (add_zero 0)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothDolbeaultLaplacianOne_eq_zero_iff
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    h.smoothDolbeaultLaplacianOne V a = 0 ↔
      h.degreeCodifferential V 0 a.val = 0 ∧ HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a = 0 :=
  ⟨h.smoothDolbeaultLaplacianOne_kernel V a,
    fun ha => h.smoothDolbeaultLaplacianOne_of_closed_coclosed V a ha.1 ha.2⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern

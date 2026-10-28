import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChartFrameCutoff
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ProjectionCoordinates

/-! # Anti Schwartz Tests -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiSchwartzTests

noncomputable section

section

/-! Arbitrary Euclidean Schwartz tests with a fixed compact chart cutoff insert into the actual original bundle with exactly their prescribed frame coefficients. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
  (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))

def holomorphicSchwartzFrameCutoff : V.analyticSpace → ℂ :=
  (ChartFrameCutoff.exists_holomorphic_chart_frame_cutoff V u e he i hg hs).choose

theorem holomorphicSchwartzFrameCutoff_smooth :
    ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ (holomorphicSchwartzFrameCutoff V u e he i g hg hs) :=
  (ChartFrameCutoff.exists_holomorphic_chart_frame_cutoff V u e he i hg hs).choose_spec.1

theorem holomorphicSchwartzFrameCutoff_support :
    tsupport (holomorphicSchwartzFrameCutoff V u e he i g hg hs) ⊆
      (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace) :=
  (ChartFrameCutoff.exists_holomorphic_chart_frame_cutoff V u e he i hg hs).choose_spec.2.1

theorem holomorphicSchwartzFrameCutoff_one (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ tsupport g) :
    holomorphicSchwartzFrameCutoff V u e he i g hg hs (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) = 1 :=
  (ChartFrameCutoff.exists_holomorphic_chart_frame_cutoff V u e he i hg hs).choose_spec.2.2 z hz

def holomorphicLineSchwartzFrameInsertion (n : ℕ) :
    𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) →ₗ[ℂ]
      HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n :=
  (HolomorphicFrame.Insertion.holomorphicLineSmoothFrameInsertion u i n (holomorphicSchwartzFrameCutoff V u e he i g hg hs)
    (holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
    (fun _ hx => (holomorphicSchwartzFrameCutoff_support V u e he i g hg hs hx).2)).comp
      (Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLinear V e he n g hg (fun _ hx => (hs hx).1))

theorem holomorphicLineSchwartzFrameInsertion_coefficients (n : ℕ)
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e n ((holomorphicLineSchwartzFrameInsertion V u e he i g hg hs n c).val i).extension z =
      g z • c z := by
  let f := holomorphicSchwartzFrameCutoff V u e he i g hg hs
  let a := Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized V e he n g hg (fun _ hx => (hs hx).1) c
  have hp := HolomorphicFrame.InsertionCoordinates.holomorphicLineSmoothFrameInsertion_coefficients V u e i n f
    (holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
    (fun _ hx => (holomorphicSchwartzFrameCutoff_support V u e he i g hg hs hx).2) a hz
  have hc : Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z = g z • c z :=
    (Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e n a.val hz.1).symm.trans
      (Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized_coefficients V e he n g hg (fun _ hx => (hs hx).1) c z)
  have hm : f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) • (g z • c z) = g z • c z := by
    by_cases hzg : z ∈ tsupport g
    · have hfone : f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) = 1 := holomorphicSchwartzFrameCutoff_one V u e he i g hg hs z hzg
      exact (congrArg (fun q : ℂ => q • (g z • c z)) hfone).trans (one_smul ℂ _)
    · rw [image_eq_zero_of_notMem_tsupport hzg, zero_smul, smul_zero]
  exact hp.trans ((congrArg (fun v => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) • v) hc).trans hm)

theorem holomorphicLineSchwartzFrameInsertion_zero (n : ℕ)
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (j : V.analyticSpace) (x : ↥(⊤ ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j))
    (hx : x.val ∉ ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e (tsupport g)) :
    (holomorphicLineSchwartzFrameInsertion V u e he i g hg hs n c).val j x = 0 :=
  HolomorphicFrame.Insertion.holomorphicLineSmoothFrameInsertion_zero_of_scalar_zero u i n _ _ _ _ j x
    (Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized_zero V e he n g hg (fun _ hy => (hs hy).1) c x.val hx)

def holomorphicLineAntiSchwartzFrameInsertion :
    𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) →ₗ[ℂ]
      HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 :=
  (OneFormProjection.holomorphicLineOneAntiProjection u ⊤).comp (holomorphicLineSchwartzFrameInsertion V u e he i g hg hs 1)

end

/-! Arbitrary compactly cut off Euclidean tests yield genuine global antiholomorphic bundle tests with the exact fixed fiber projection and support. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
  (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))

theorem holomorphicLineSchwartzFrameInsertion_covector (n : ℕ)
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n ((holomorphicLineSchwartzFrameInsertion V u e he i g hg hs n c).val i).extension z =
      (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n).symm (g z • c z) := by
  have hc := holomorphicLineSchwartzFrameInsertion_coefficients V u e he i g hg hs n c hz
  apply (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n).injective
  exact hc.trans (ContinuousLinearEquiv.apply_symm_apply _ _).symm

theorem holomorphicLineAntiSchwartzFrameInsertion_covector
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 ((holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c).val.val i).extension z =
      g z • OneCovectorAntiProjection.oneCovectorAntiProjection
        ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1).symm (c z)) := by
  have hp := ProjectionCoordinates.holomorphicLineOnePart_covector V u e he ⊤
    (holomorphicLineSchwartzFrameInsertion V u e he i g hg hs 1 c) i
    (show z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (⊤ ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
      from ⟨hz.1, trivial, hz.2⟩)
  have hc := holomorphicLineSchwartzFrameInsertion_covector V u e he i g hg hs 1 c hz
  have hm := (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1).symm.map_smul (g z) (c z)
  exact hp.trans ((congrArg OneCovectorAntiProjection.oneCovectorAntiProjection (hc.trans hm)).trans (OneCovectorAntiProjection.oneCovectorAntiProjection_complex_smul _ _))

theorem holomorphicLineAntiSchwartzFrameInsertion_zero
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (j : V.analyticSpace) (x : ↥(⊤ ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j))
    (hx : x.val ∉ ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e (tsupport g)) :
    (holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c).val.val j x = 0 := by
  have hzero := holomorphicLineSchwartzFrameInsertion_zero V u e he i g hg hs 1 c j x hx
  change Manifold.OneFormProjection.openManifoldOnePart Complex.I ((holomorphicLineSchwartzFrameInsertion V u e he i g hg hs 1 c).val j) x = 0
  rw [OneFormProjection.openManifoldOnePart_apply, hzero]
  apply ContinuousAlternatingMap.ext
  intro t
  change (1 / 2 : ℂ) * (0 + Complex.I * 0) = 0
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiSchwartzTests

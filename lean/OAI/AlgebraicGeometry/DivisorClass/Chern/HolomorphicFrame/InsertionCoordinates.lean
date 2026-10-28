import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Insertion
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.CoordinatesLp

/-! # Insertion Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.InsertionCoordinates

noncomputable section

/-! In the chosen original holomorphic frame, the inserted global test has exactly the cutoff Euclidean coefficients of its scalar source. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem holomorphicLineSmoothFrameInsertion_covector (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace) (n : ℕ)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Set V.analyticSpace))
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n ((Insertion.holomorphicLineSmoothFrameInsertion u i n f hf hs a).val i).extension z =
      f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) • Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n a.val z := by
  have hp : ((Insertion.holomorphicLineSmoothFrameInsertion u i n f hf hs a).val i).extension (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) =
      f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) • a (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) :=
    (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply ((Insertion.holomorphicLineSmoothFrameInsertion u i n f hf hs a).val i)
      ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, trivial, hz.2⟩).trans
      (Insertion.holomorphicLineSmoothFrameInsertion_in_frame u i n f hf hs a _)
  dsimp only [Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse] at hp
  unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
  rw [hp]
  ext t
  rfl

theorem holomorphicLineSmoothFrameInsertion_coefficients (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace) (n : ℕ)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Set V.analyticSpace))
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e n ((Insertion.holomorphicLineSmoothFrameInsertion u i n f hf hs a).val i).extension z =
      f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) • Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z := by
  unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients
  rw [holomorphicLineSmoothFrameInsertion_covector V u e i n f hf hs a hz, map_smul]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.InsertionCoordinates

import OAI.Analysis.HodgeTheory.Decomposition.AdjointAlgebra

/-! # Adjoint Locality -/

namespace OAI.Analysis.HodgeTheory.Decomposition.AdjointLocality.Constructions

noncomputable section

/-! The constructed global codifferential agrees with its explicit formula
in every chart. This follows from its actual L² identity and smooth cutoffs. -/

open scoped ContDiff _root_.Manifold _root_.Topology
open _root_.MeasureTheory

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem exists_projective_cutoff_at {U : Set V.analyticSpace} (hU : IsOpen U)
    (x : V.analyticSpace) (hx : x ∈ U) :
    ∃ f : V.analyticSpace → ℂ,
      ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f ∧ tsupport f ⊆ U ∧ f x = 1 := by
  obtain ⟨g, _, hg⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, V.analyticModel)) x).mem_iff.mp
    (hU.mem_nhds hx)
  refine ⟨fun y => (g y : ℂ), Complex.ofRealCLM.contDiff.contMDiff.comp g.contMDiff, ?_, ?_⟩
  · have hs : tsupport (fun y => (g y : ℂ)) = tsupport g := by
      apply congrArg closure
      ext y
      simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
    rw [hs]
    exact hg
  · change (g x : ℂ) = 1
    rw [g.eq_one, Complex.ofReal_one]

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

theorem projectiveRealL2Pair_separates_left
    (a b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (h : ∀ u, (Form.Constructions.projectiveL2Pair V n a u).re = (Form.Constructions.projectiveL2Pair V n b u).re) : a = b := by
  apply sub_eq_zero.mp
  apply AdjointAlgebra.Constructions.projectiveL2Pair_self_re_nonpos V n
  rw [AdjointAlgebra.Constructions.projectiveL2Pair_sub_left, Complex.sub_re, h (a - b), sub_self]

omit [BorelSpace V.analyticSpace] in
theorem projectiveL2Pair_smulFunction_move
    (a b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f) :
    Form.Constructions.projectiveL2Pair V n a (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f hf b) =
      Form.Constructions.projectiveL2Pair V n
        (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction (fun x => star (f x)) (AdjointManifold.Constructions.conjugateFunction_smooth V f hf) a) b := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (AdjointManifold.Constructions.projectiveFormPointPair_smulFunction_move V n a.val b.val f)

theorem weightedProjectiveChartAdjoint_eq_global
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ e.source)
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    AdjointManifold.Constructions.weightedProjectiveChartAdjoint V n e he f hf hs b =
      DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction (fun x => star (f x)) (AdjointManifold.Constructions.conjugateFunction_smooth V f hf)
        (AdjointAlgebra.Constructions.projectiveCodifferential V n b) := by
  apply projectiveRealL2Pair_separates_left V n
  intro a
  rw [← AdjointManifold.Constructions.weightedProjectiveChartAdjoint_pair, AdjointAlgebra.Constructions.projectiveCodifferential_pair,
    projectiveL2Pair_smulFunction_move]

/-- Every chart gives the same genuine codifferential, with no chosen-cover restriction. -/
theorem projectiveCodifferential_eq_chart
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (x : V.analyticSpace) (hx : x ∈ e.source) :
    AdjointAlgebra.Constructions.projectiveCodifferential V n b x = LocalAdjointForm.Constructions.projectiveChartAdjoint V e n b x := by
  obtain ⟨f, hf, hs, hfx⟩ := exists_projective_cutoff_at V e.open_source x hx
  have h := congrArg (fun a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n => a x)
    (weightedProjectiveChartAdjoint_eq_global V n e he f hf hs b)
  change star (f x) • LocalAdjointForm.Constructions.projectiveChartAdjoint V e n b x =
    star (f x) • AdjointAlgebra.Constructions.projectiveCodifferential V n b x at h
  rw [hfx, star_one, one_smul, one_smul] at h
  exact h.symm

omit [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] in
theorem euclideanChartCoefficients_congr_at
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a b : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (h : a (MeasureVolume.Constructions.chartCoordinateInverse V e z) = b (MeasureVolume.Constructions.chartCoordinateInverse V e z)) :
    EuclideanForms.Constructions.euclideanChartCoefficients V e n a z = EuclideanForms.Constructions.euclideanChartCoefficients V e n b z := by
  have hc : a.inChart e (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) = b.inChart e (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) := by
    unfold DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
    change (a (MeasureVolume.Constructions.chartCoordinateInverse V e z)).compContinuousLinearMap _ =
      (b (MeasureVolume.Constructions.chartCoordinateInverse V e z)).compContinuousLinearMap _
    rw [h]
  rw [EuclideanForms.Constructions.euclideanChartCoefficients_eq_analytic, EuclideanForms.Constructions.euclideanChartCoefficients_eq_analytic, hc]

/-- The global codifferential has precisely the smooth local coefficient formula derived by integration. -/
theorem projectiveCodifferential_coefficients
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    EuclideanForms.Constructions.euclideanChartCoefficients V e n (AdjointAlgebra.Constructions.projectiveCodifferential V n b).val z =
      AdjointCoefficients.Constructions.projectiveLocalAdjointCoefficients V e n (EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) b.val) z := by
  have h := euclideanChartCoefficients_congr_at V n e (AdjointAlgebra.Constructions.projectiveCodifferential V n b).val
    (LocalAdjointForm.Constructions.projectiveChartAdjoint V e n b) z
      (projectiveCodifferential_eq_chart V n e he b (MeasureVolume.Constructions.chartCoordinateInverse V e z) (e.map_target hz))
  exact h.trans (LocalAdjointForm.Constructions.projectiveChartAdjoint_coefficients V e he n b z hz)

end

end OAI.Analysis.HodgeTheory.Decomposition.AdjointLocality.Constructions

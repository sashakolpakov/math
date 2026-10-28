import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AdjointPair
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothPoisson

/-! # Harmonic One Forms -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HarmonicOneForms.CM.Construction

noncomputable section

/-! Every smooth one-form has an exact correction which is coclosed.
For a closed input the corrected form is both closed and coclosed. -/

open _root_.MeasureTheory

theorem exists_smooth_coclosed_correction (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) :
    ∃ f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0,
      Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 (a - Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f) = 0 := by
  let F := Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 a
  have hF : ∀ c : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0,
      IsLocallyConstant (HolomorphicPrimitive.CM.Construction.zeroFormScalar c) → inner ℝ (GlobalLp.CM.Construction.varietySmoothScalarL2 V F) (GlobalLp.CM.Construction.varietySmoothScalarL2 V c) = 0 := by
    intro c hc
    rw [← AdjointPair.CM.Construction.adjointL2Pair_zero_re]
    change (Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 0 (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 a) c).re = 0
    rw [← Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential_pair V 0 c a,
      HolomorphicPrimitive.CM.Construction.d_zeroForm_eq_zero_of_locallyConstant c hc, Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveL2Pair_zero_right, Complex.zero_re]
  obtain ⟨f, hf⟩ := SmoothPoisson.CM.Construction.variety_smooth_poisson_exists V C b F hF
  let r := Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 (a - Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f)
  have hpair (v : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) :
      inner ℝ (GlobalLp.CM.Construction.varietySmoothScalarL2 V r) (GlobalLp.CM.Construction.varietySmoothScalarL2 V v) = 0 := by
    calc
      _ = (Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 1 (a - Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d v)).re := by
        rw [← AdjointPair.CM.Construction.adjointL2Pair_zero_re, Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential_pair]
      _ = (Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 1 a (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d v)).re -
          (Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 1 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d v)).re := by
        rw [Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveL2Pair_sub_left, Complex.sub_re]
      _ = inner ℝ (GlobalLp.CM.Construction.varietySmoothScalarL2 V F) (GlobalLp.CM.Construction.varietySmoothScalarL2 V v) -
          inner ℝ (GlobalLp.CM.Construction.varietySmoothScalarL2 V F) (GlobalLp.CM.Construction.varietySmoothScalarL2 V v) := by
        rw [Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential_pair, AdjointPair.CM.Construction.adjointL2Pair_zero_re,
          AdjointPair.CM.Construction.adjointL2Pair_one_re V C b, hf v]
      _ = 0 := sub_self _
  refine ⟨f, GlobalLp.CM.Construction.varietySmoothScalarL2_injective V ?_⟩
  rw [map_zero]
  have h := hpair r
  rw [real_inner_self_eq_norm_sq] at h
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h)

theorem exists_closed_coclosed_representative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0) :
    ∃ f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0,
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (a - Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f) = 0 ∧
      Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 (a - Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f) = 0 := by
  obtain ⟨f, hf⟩ := exists_smooth_coclosed_correction V C b a
  refine ⟨f, ?_, hf⟩
  rw [map_sub, ha, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_squared, sub_zero]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HarmonicOneForms.CM.Construction

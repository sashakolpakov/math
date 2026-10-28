import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalSmoothSolution
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothOneFormFaithful
import OAI.Analysis.DifferentialForms.Manifold.LocallyConstant

/-! # Derivative Kernel -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DerivativeKernel.CM.Construction

noncomputable section

/-! The actual completed derivative kernel consists exactly of smooth
locally constant scalar functions. No connectedness is assumed here. -/

open Set _root_.TopologicalSpace

theorem zeroFormScalar_locallyConstant_of_d_zero (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) (hf : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f = 0) :
    IsLocallyConstant (HolomorphicPrimitive.CM.Construction.zeroFormScalar f) := by
  have hd : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (⊤ : Opens V.analyticSpace) f) = 0 := by
    rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_d, hf, map_zero]
  have hlocal := (Analysis.DifferentialForms.Manifold.LocallyConstant.d_openManifoldZeroForm_eq_zero_iff
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (⊤ : Opens V.analyticSpace) f)).mp hd
  apply Analysis.DifferentialForms.Manifold.LocallyConstant.isLocallyConstant_of_openNeighborhoods
  intro x
  exact ⟨⊤, mem_univ x, hlocal⟩

theorem derivative_eq_zero_iff_locallyConstant (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (u : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b) :
    GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b u = 0 ↔
      ∃ f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0,
        GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev V C b f = u ∧ IsLocallyConstant (HolomorphicPrimitive.CM.Construction.zeroFormScalar f) := by
  constructor
  · intro hu
    obtain ⟨f, hf⟩ := GlobalSmoothSolution.CM.Construction.derivative_kernel_smooth V C b u hu
    have hd : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f = 0 := by
      apply SmoothOneFormFaithful.CM.Construction.varietyOneFormL2_eq_zero_imp V C b
      have h := congrArg (GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b) hf
      rw [GlobalSobolevGraph.CM.Construction.varietySobolevDerivative_smooth, hu] at h
      exact h
    exact ⟨f, hf, zeroFormScalar_locallyConstant_of_d_zero V f hd⟩
  · rintro ⟨f, rfl, hf⟩
    rw [GlobalSobolevGraph.CM.Construction.varietySobolevDerivative_smooth]
    rw [HolomorphicPrimitive.CM.Construction.d_zeroForm_eq_zero_of_locallyConstant f hf, map_zero]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DerivativeKernel.CM.Construction

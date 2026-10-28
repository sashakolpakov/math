import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallClosed
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.InitialTensor

/-! # Total Ball Forms -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalBallForms.CM

noncomputable section

/-!
ThetaCycle: actual pure closed top forms for every fixed total finite Schwartz input.
The native TensorDecomposition finite tensor decomposition and GaussianConvergence Hessian additivity identify
their chart coefficients with the literal projected total theta Hessian.
-/

open scoped Classical _root_.Manifold ContDiff BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

def chartFormValue {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (n : ℕ)
    (e : OpenPartialHomeomorph M E) (z : E) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n where
  toFun form := form.val.inChart e z
  map_add' a b := congrArg (fun f => f z) (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add a.val b.val e)
  map_smul' c a := congrArg (fun f => f z) (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul c a.val e)

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d₀ d₁ : Gal(K/ℚ) → Bool}

theorem split_theta_sum
    (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
    (Φ : HeckeCycles.GeometricSource.CM.FiniteInput (Sum (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places)))
    (n : ℕ) (Ψ : Fin n → HeckeCycles.GeometricSource.CM.FiniteInput (Sum (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places)))
    (hΨ : ∀ a, Φ.val a = ∑ i, (Ψ i).val a) (z : HeckeCycles.GeometricSource.CM.BallChart) :
    InitialTensor.CM.splitThetaTopCoefficient K L₀ L₁ Φ z = ∑ i, InitialTensor.CM.splitThetaTopCoefficient K L₀ L₁ (Ψ i) z := by
  have hh (v : Fin 2 → (Sum (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) → ℂ)) :=
    RepresentationTheory.Theta.Kernel.Factorization.completed_hessian_sum (IntrinsicAnalysis.CM.nativeGaussianConvergenceInput _) Φ n Ψ hΨ
      (BlockPeriod.CM.blockPeriod (L₀.period z) (L₁.period z)) v
  simp only [IntrinsicAnalysis.CM.c38_completed_eq] at hh
  simp only [InitialTensor.CM.splitThetaTopCoefficient, RepresentationTheory.Theta.Kernel.Calculus.doubleAlt, InitialTensor.CM.splitThetaTensor, hh, Finset.mul_sum,
    ← Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

/-- A full finite tensor factorization of the actual total theta coefficient. -/
theorem total_theta_coefficient_factorization
    (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
    (Φ : HeckeCycles.GeometricSource.CM.FiniteInput (Sum (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places))) :
    ∃ (n : ℕ) (φ ψ : Fin n → HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)),
      (∀ a, Φ.val a = ∑ i, (φ i).val (fun j => a (Sum.inl j)) *
        (ψ i).val (fun j => a (Sum.inr j))) ∧
      ∀ z, InitialTensor.CM.splitThetaTopCoefficient K L₀ L₁ Φ z =
        ∑ i, Slots.CM.sourceWedgeCoefficient K L₀ L₁ (φ i) (ψ i) z := by
  obtain ⟨n, φ, ψ, h⟩ := RepresentationTheory.Theta.Kernel.Factorization.tensor_decomposition (RepresentationTheory.Theta.Kernel.Schwartz.e32_coordinates (IntrinsicAnalysis.CM.nativeTensorDecompositionProductInput _ _)) Φ
  refine ⟨n, φ, ψ, h, fun z => ?_⟩
  have hsum : ∀ a, Φ.val a = ∑ i, (RepresentationTheory.Theta.Factorization.Derivative.tensorInput (φ i) (ψ i)).val a := h
  rw [split_theta_sum K L₀ L₁ Φ n _ hsum z]
  simp only [InitialTensor.CM.split_theta_tensor_factorization]

/-- The literal total theta Hessian represents a smooth, pure, closed form on
the actual ball. The same finite input is retained throughout the conclusion. -/
theorem exists_total_ball_top_form
    (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
    (Φ : HeckeCycles.GeometricSource.CM.FiniteInput (Sum (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places))) :
    ∃ form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart B.Domain 2,
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart B.Domain 2 0 form.val ∧
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form = 0 ∧
      ∀ (e : OpenPartialHomeomorph B.Domain HeckeCycles.GeometricSource.CM.BallChart), e ∈ atlas HeckeCycles.GeometricSource.CM.BallChart B.Domain →
        ∀ z ∈ B.domain, form.val.inChart e z (Pi.basisFun ℂ (Fin 2)) =
          InitialTensor.CM.splitThetaTopCoefficient K L₀ L₁ Φ z := by
  obtain ⟨n, φ, ψ, _, hsum⟩ := total_theta_coefficient_factorization K L₀ L₁ Φ
  let form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart B.Domain 2 := ∑ i, BallForms.CM.sourceBallTwoForm K L₀ L₁ (φ i) (ψ i)
  refine ⟨form, ?_, ?_, ?_⟩
  · exact (Analysis.DifferentialForms.Manifold.ManifoldBidegree.pureManifoldFormSubmodule HeckeCycles.GeometricSource.CM.BallChart B.Domain 2 0).sum_mem
      (fun i _ => BallForms.CM.source_ball_two_pure K L₀ L₁ (φ i) (ψ i))
  · simp only [form, map_sum, BallClosed.CM.source_ball_two_closed, Finset.sum_const_zero]
  · intro e he z hz
    change chartFormValue 2 e z form (Pi.basisFun ℂ (Fin 2)) = _
    dsimp only [form]
    rw [map_sum, hsum]
    rw [ContinuousAlternatingMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact BallForms.CM.source_ball_two_coefficient K L₀ L₁ (φ i) (ψ i) e he hz

theorem exists_nonzero_total_ball_top_form [IsGalois ℚ K]
    (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁) (z : B.Domain) :
    ∃ (Φ : HeckeCycles.GeometricSource.CM.FiniteInput (Sum (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places)))
      (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart B.Domain 2),
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart B.Domain 2 0 form.val ∧
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form = 0 ∧ form ≠ 0 ∧
      ∀ (e : OpenPartialHomeomorph B.Domain HeckeCycles.GeometricSource.CM.BallChart), e ∈ atlas HeckeCycles.GeometricSource.CM.BallChart B.Domain →
        ∀ y ∈ B.domain, form.val.inChart e y (Pi.basisFun ℂ (Fin 2)) =
          InitialTensor.CM.splitThetaTopCoefficient K L₀ L₁ Φ y := by
  obtain ⟨Φ, hΦ⟩ := InitialTensor.CM.exists_initial_total_theta_nonzero K L₀ L₁ z z.property
  obtain ⟨form, hp, hc, he⟩ := exists_total_ball_top_form K L₀ L₁ Φ
  refine ⟨Φ, form, hp, hc, ?_, he⟩
  intro hzero
  have h := he (chartAt HeckeCycles.GeometricSource.CM.BallChart z) (chart_mem_atlas HeckeCycles.GeometricSource.CM.BallChart z) z z.property
  rw [hzero] at h
  exact hΦ h.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalBallForms.CM

import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverDerivative
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DoubleCauchy

/-! # Cover Smooth -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverSmooth.CM

noncomputable section

/-! Smoothness of the native holomorphic covering maps follows from
the two-variable Cauchy regularity theorem in fixed local charts. -/

open scoped Classical _root_.Manifold ContDiff _root_.Topology
open Filter
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DoubleCauchy.CM.HolomorphicRegularity

section Charts

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold 𝓘(ℂ, V) 1 M]
  [TopologicalSpace N] [ChartedSpace W N] [IsManifold 𝓘(ℂ, W) 1 N]

/-- Holomorphicity on a complex surface implies smoothness into any
finite-dimensional complex manifold, using the existing native atlas. -/
theorem contMDiff_of_model_equiv (eV : V ≃L[ℂ] GeometricSource.CM.BallChart) {f : M → N}
    (hf : MDifferentiable 𝓘(ℂ, V) 𝓘(ℂ, W) f) :
    ContMDiff 𝓘(ℂ, V) 𝓘(ℂ, W) ∞ f := by
  intro x
  let a := chartAt V x
  let b := chartAt W (f x)
  let F : V → W := b ∘ f ∘ a.symm
  have hax : a.symm (a x) = x := a.left_inv (mem_chart_source V x)
  have hc : ContinuousAt (fun w => f (a.symm w)) (a x) :=
    (hf (a.symm (a x))).continuousAt.comp
      (a.symm.continuousAt (mem_chart_target V x))
  have hb : {w | f (a.symm w) ∈ b.source} ∈ nhds (a x) := by
    apply hc.preimage_mem_nhds
    rw [hax]
    exact chart_source_mem_nhds W (f x)
  have hd : ∀ᶠ w in nhds (a x), DifferentiableAt ℂ F w := by
    filter_upwards [a.open_target.mem_nhds (mem_chart_target V x), hb] with w hw hfw
    have h := (mdifferentiableAt_iff_of_mem_source
      (I := 𝓘(ℂ, V)) (I' := 𝓘(ℂ, W))
      (f := f) (x := x) (y := f x) (a.map_target hw) hfw).mp (hf (a.symm w))
    have he := a.right_inv hw
    simpa only [F, a, b, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.id_comp, Function.comp_id, Set.range_id, differentiableWithinAt_univ, he]
      using h.2
  have hs := DoubleCauchy.CM.HolomorphicRegularity.equiv_finTwo_contDiffAt_of_eventually_differentiableAt eV hd
  apply contMDiffAt_iff.mpr
  refine ⟨(hf x).continuousAt, ?_⟩
  simpa only [F, a, b, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.range_id, contDiffWithinAt_univ] using hs

end Charts

/-- The source covering has the literal two-dimensional model. -/
theorem twoDimensional_contMDiff
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace GeometricSource.CM.BallChart M]
    [IsManifold 𝓘(ℂ, GeometricSource.CM.BallChart) 1 M]
    [TopologicalSpace N] [ChartedSpace W N] [IsManifold 𝓘(ℂ, W) 1 N]
    {f : M → N} (hf : MDifferentiable 𝓘(ℂ, GeometricSource.CM.BallChart) 𝓘(ℂ, W) f) :
    ContMDiff 𝓘(ℂ, GeometricSource.CM.BallChart) 𝓘(ℂ, W) ∞ f :=
  contMDiff_of_model_equiv (ContinuousLinearEquiv.refl ℂ GeometricSource.CM.BallChart) hf

/-- The ball contains the zero negative line in its fixed affine chart. -/
def ballBasePoint
    {E : IntermediateField ℚ ℂ} [NumberField E] [NumberField.IsCMField E]
    (B : GeometricSource.CM.BallDatum E) : B.Domain :=
  ⟨0, by
    change Complex.normSq 0 + Complex.normSq 0 < -(B.b : ℂ).re
    simpa only [Complex.normSq_zero, zero_add] using neg_pos.mpr B.negative⟩

/-- The covering derivative identifies the target's native tangent model
with the two-dimensional ball model. Thus every holomorphic map out of
that quotient is complex smooth and real smooth. -/
theorem quotient_map_contMDiff
    {E : IntermediateField ℚ ℂ} [NumberField E] [NumberField.IsCMField E]
    (B : GeometricSource.CM.BallDatum E) (N : ℕ) (X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : B.Domain → X.analyticSpace) (hπ : B.IsBallCover N X π)
    (f : X.analyticSpace → Y.analyticSpace)
    (hf : MDifferentiable 𝓘(ℂ, X.analyticModel) 𝓘(ℂ, Y.analyticModel) f) :
    ContMDiff 𝓘(ℂ, X.analyticModel) 𝓘(ℂ, Y.analyticModel) ∞ f ∧
      ContMDiff 𝓘(ℝ, X.analyticModel) 𝓘(ℝ, Y.analyticModel) ∞ f := by
  let z := ballBasePoint B
  let D : GeometricSource.CM.BallChart →L[ℂ] X.analyticModel :=
    mfderiv 𝓘(ℂ, GeometricSource.CM.BallChart) 𝓘(ℂ, X.analyticModel) π z
  let A : GeometricSource.CM.BallChart ≃L[ℂ] X.analyticModel :=
    (LinearEquiv.ofBijective D.toLinearMap
      (hπ.2.2.2.2.1 z)).toContinuousLinearEquiv
  have hs := contMDiff_of_model_equiv A.symm hf
  exact ⟨hs, Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hs⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverSmooth.CM

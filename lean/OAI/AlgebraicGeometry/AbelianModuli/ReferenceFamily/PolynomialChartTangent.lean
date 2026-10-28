import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GraphChartTangent
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity

/-! # Polynomial Chart Tangent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PolynomialChartTangent

noncomputable section

/-! The existing analytic chart on a regular polynomial zero set can
be retained together with its actual derivative isomorphism. -/

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity
open scoped ContDiff

theorem exists_polynomial_chart_tangent
    {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : σ → MvPolynomial (ι ⊕ σ) ℂ) (x : (ι → ℂ) × (σ → ℂ))
    (hx : ComplexPoints.Analytic.PolynomialImplicit.splitPolynomialMap P x = 0)
    (hreg : ((fderiv ℂ (ComplexPoints.Analytic.PolynomialImplicit.splitPolynomialMap P) x).comp
      (ContinuousLinearMap.inr ℂ (ι → ℂ) (σ → ℂ))).IsInvertible) :
    ∃ e : OpenPartialHomeomorph {z | ComplexPoints.Analytic.PolynomialImplicit.splitPolynomialMap P z = 0} (ι → ℂ),
      (⟨x, hx⟩ : {z | ComplexPoints.Analytic.PolynomialImplicit.splitPolynomialMap P z = 0}) ∈ e.source ∧
      (∀ z, e z = z.val.1) ∧
      ContDiffOn ℂ ω (fun u => (e.symm u).val) e.target ∧
      ∃ d : (ι → ℂ) ≃ₗ[ℂ] (fderiv ℂ (ComplexPoints.Analytic.PolynomialImplicit.splitPolynomialMap P) x).toLinearMap.ker,
        ∀ u, (d u).val = fderiv ℂ (fun u => (e.symm u).val) (e ⟨x, hx⟩) u := by
  obtain ⟨e, he, hproj, hd⟩ := ComplexPoints.Analytic.LocalGraphChart.exists_polynomial_zero_chart P x hx hreg
  refine ⟨e, he, hproj, hd, ?_⟩
  exact GraphChartTangent.graphChart_tangent_equiv (ComplexPoints.Analytic.PolynomialImplicit.splitPolynomialMap P) e ⟨x, hx⟩ he hproj hd
    ((ComplexPoints.Analytic.PolynomialImplicit.contDiff_splitPolynomialMap P 1).differentiable_one x) hreg

theorem exists_standardSmooth_chart_tangent
    {S ι σ : Type*} [CommRing S] [Algebra ℂ S] [Fintype ι] [Fintype σ] [DecidableEq ι]
    (P : Algebra.SubmersivePresentation ℂ S ι σ) (x : S →ₐ[ℂ] ℂ) :
    let Q := ComplexPoints.Analytic.JacobianRegularity.presentationSplitPolynomials P.toPreSubmersivePresentation
    let z := ComplexPoints.Analytic.JacobianRegularity.presentationSplitPoint P.toPreSubmersivePresentation x
    ∃ e : OpenPartialHomeomorph {y | ComplexPoints.Analytic.PolynomialImplicit.splitPolynomialMap Q y = 0} (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ),
      (⟨z, ComplexPoints.Analytic.JacobianRegularity.presentationSplitPoint_zero P.toPreSubmersivePresentation x⟩ :
        {y | ComplexPoints.Analytic.PolynomialImplicit.splitPolynomialMap Q y = 0}) ∈ e.source ∧
      (∀ y, e y = y.val.1) ∧
      ContDiffOn ℂ ω (fun u => (e.symm u).val) e.target ∧
      ∃ d : (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ) ≃ₗ[ℂ] (fderiv ℂ (ComplexPoints.Analytic.PolynomialImplicit.splitPolynomialMap Q) z).toLinearMap.ker,
        ∀ u, (d u).val = fderiv ℂ (fun u => (e.symm u).val)
          (e ⟨z, ComplexPoints.Analytic.JacobianRegularity.presentationSplitPoint_zero P.toPreSubmersivePresentation x⟩) u :=
  exists_polynomial_chart_tangent _ _ (ComplexPoints.Analytic.JacobianRegularity.presentationSplitPoint_zero P.toPreSubmersivePresentation x)
    (ComplexPoints.Analytic.JacobianRegularity.standardSmooth_partialDerivative_isInvertible P x)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PolynomialChartTangent

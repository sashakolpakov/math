import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PresentedAlgebra
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PolynomialChartTangent

/-! # Presentation Tangent Splitting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PresentationTangentSplitting

noncomputable section

/-! The native selected/free coordinate splitting identifies the
linearized presentation ideal with the actual analytic graph kernel. -/

open scoped ContDiff

variable {S ι σ : Type*} [CommRing S] [Algebra ℂ S]
  [Fintype ι] [Fintype σ] [DecidableEq ι]

theorem presentationSplit_derivative (P : Algebra.PreSubmersivePresentation ℂ S ι σ)
    (x v : ι → ℂ) :
    fderiv ℂ (ComplexPoints.Analytic.PolynomialImplicit.splitPolynomialMap (ComplexPoints.Analytic.JacobianRegularity.presentationSplitPolynomials P))
      (ComplexPoints.Analytic.JacobianRegularity.selectedCoordinateEquiv P.map P.map_inj x)
      (ComplexPoints.Analytic.JacobianRegularity.selectedCoordinateEquiv P.map P.map_inj v) = Dual.QuotientPoints.polynomialJacobianMap P.relation x v := by
  let c := ComplexPoints.Analytic.JacobianRegularity.selectedCoordinateEquiv P.map P.map_inj
  let F := ComplexPoints.Analytic.PolynomialImplicit.splitPolynomialMap (ComplexPoints.Analytic.JacobianRegularity.presentationSplitPolynomials P)
  have hc : (F ∘ c) = fun y => fun j => MvPolynomial.eval y (P.relation j) := by
    funext y j
    exact ComplexPoints.Analytic.JacobianRegularity.selectedPolynomialFamily_eval P.map P.map_inj P.relation y j
  have hd : HasFDerivAt (fun y => fun j => MvPolynomial.eval y (P.relation j))
      ((fderiv ℂ F (c x)).comp c.toContinuousLinearMap) x := by
    rw [← hc]
    exact ((ComplexPoints.Analytic.PolynomialImplicit.contDiff_splitPolynomialMap (ComplexPoints.Analytic.JacobianRegularity.presentationSplitPolynomials P) 1).differentiable_one (c x)).hasFDerivAt.comp
      x c.hasFDerivAt
  funext j
  have hj := (hasFDerivAt_apply j (fun k => MvPolynomial.eval x (P.relation k))).comp x hd
  have he := hj.unique (ComplexPoints.Analytic.PolynomialDerivative.differentiable_polynomial_eval (P.relation j) x).hasFDerivAt
  exact DFunLike.congr_fun he v

theorem presentationTangent_mem (P : Algebra.PreSubmersivePresentation ℂ S ι σ)
    (x : S →ₐ[ℂ] ℂ) (v : ι → ℂ) :
    v ∈ Dual.QuotientPoints.polynomialRelationTangent P.ker (fun i => x (P.val i)) ↔
      fderiv ℂ (ComplexPoints.Analytic.PolynomialImplicit.splitPolynomialMap (ComplexPoints.Analytic.JacobianRegularity.presentationSplitPolynomials P))
        (ComplexPoints.Analytic.JacobianRegularity.presentationSplitPoint P x) (ComplexPoints.Analytic.JacobianRegularity.selectedCoordinateEquiv P.map P.map_inj v) = 0 := by
  have hker := Dual.QuotientPoints.polynomialRelationTangent_eq_kernel P.relation (fun i => x (P.val i))
    (Foundations.Scheme.StandardSmoothJacobian.Algebraic.point_relation_zero P.toPresentation x)
  rw [P.span_range_relation_eq_ker] at hker
  rw [hker]
  change Dual.QuotientPoints.polynomialJacobianMap P.relation (fun i => x (P.val i)) v = 0 ↔ _
  exact iff_of_eq (congrArg (fun w => w = 0) (presentationSplit_derivative P (fun i => x (P.val i)) v)).symm

def presentationTangentSplitEquiv (P : Algebra.PreSubmersivePresentation ℂ S ι σ)
    (x : S →ₐ[ℂ] ℂ) :
    Dual.QuotientPoints.polynomialRelationTangent P.ker (fun i => x (P.val i)) ≃ₗ[ℂ]
      (fderiv ℂ (ComplexPoints.Analytic.PolynomialImplicit.splitPolynomialMap (ComplexPoints.Analytic.JacobianRegularity.presentationSplitPolynomials P))
        (ComplexPoints.Analytic.JacobianRegularity.presentationSplitPoint P x)).toLinearMap.ker where
  toFun v := ⟨ComplexPoints.Analytic.JacobianRegularity.selectedCoordinateEquiv P.map P.map_inj v.val, (presentationTangent_mem P x v.val).mp v.property⟩
  invFun w := ⟨(ComplexPoints.Analytic.JacobianRegularity.selectedCoordinateEquiv P.map P.map_inj).symm w.val, by
    apply (presentationTangent_mem P x _).mpr
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact w.property⟩
  left_inv v := Subtype.ext ((ComplexPoints.Analytic.JacobianRegularity.selectedCoordinateEquiv P.map P.map_inj).symm_apply_apply v.val)
  right_inv w := Subtype.ext ((ComplexPoints.Analytic.JacobianRegularity.selectedCoordinateEquiv P.map P.map_inj).apply_symm_apply w.val)
  map_add' v w := Subtype.ext ((ComplexPoints.Analytic.JacobianRegularity.selectedCoordinateEquiv P.map P.map_inj).map_add v.val w.val)
  map_smul' a v := Subtype.ext ((ComplexPoints.Analytic.JacobianRegularity.selectedCoordinateEquiv P.map P.map_inj).map_smul a v.val)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PresentationTangentSplitting

import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PresentationTangentSplitting
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PresentedPointDifferential

/-! # Standard Smooth Dual Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StandardSmoothDualCoordinates

noncomputable section

/-! Actual dual-number points of a standard-smooth algebra are
parametrized by its native free tangent coordinates. -/

variable {S ι σ : Type*} [CommRing S] [Algebra ℂ S]
  [Fintype ι] [Fintype σ] [DecidableEq ι]

def standardSmoothTangentFreeEquiv (P : Algebra.SubmersivePresentation ℂ S ι σ)
    (x : S →ₐ[ℂ] ℂ) :
    Dual.QuotientPoints.polynomialRelationTangent P.ker (fun i => x (P.val i)) ≃ₗ[ℂ] (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ) := by
  let F := fderiv ℂ (ComplexPoints.Analytic.PolynomialImplicit.splitPolynomialMap (ComplexPoints.Analytic.JacobianRegularity.presentationSplitPolynomials P.toPreSubmersivePresentation))
    (ComplexPoints.Analytic.JacobianRegularity.presentationSplitPoint P.toPreSubmersivePresentation x)
  let h := ComplexPoints.Analytic.JacobianRegularity.standardSmooth_partialDerivative_isInvertible P x
  let r := h.choose
  have he (v : σ → ℂ) : F.toLinearMap (0, v) = r v := DFunLike.congr_fun h.choose_spec.symm v
  exact (PresentationTangentSplitting.presentationTangentSplitEquiv P.toPreSubmersivePresentation x).trans
    (KernelGraphCoordinates.kernelFreeEquiv F.toLinearMap r.toLinearEquiv he)

theorem standardSmoothTangentFreeEquiv_apply (P : Algebra.SubmersivePresentation ℂ S ι σ)
    (x : S →ₐ[ℂ] ℂ) (v : Dual.QuotientPoints.polynomialRelationTangent P.ker (fun i => x (P.val i)))
    (i : ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map) : standardSmoothTangentFreeEquiv P x v i = v.val i.val := rfl

def standardSmoothDualPointsEquiv (P : Algebra.SubmersivePresentation ℂ S ι σ)
    (x : S →ₐ[ℂ] ℂ) : (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ) ≃ Dual.PresentedAlgebra.DualAlgebraPoints x :=
  (standardSmoothTangentFreeEquiv P x).symm.toEquiv.trans (Dual.PresentedAlgebra.presentedDualPointsEquiv P.toPresentation x)

theorem standardSmoothDualPointsEquiv_inverse (P : Algebra.SubmersivePresentation ℂ S ι σ)
    (x : S →ₐ[ℂ] ℂ) (f : Dual.PresentedAlgebra.DualAlgebraPoints x) (i : ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map) :
    (standardSmoothDualPointsEquiv P x).symm f i = (f.val (P.val i.val)).snd :=
  Dual.PresentedAlgebra.presentedDualPointsEquiv_inverse P.toPresentation x f i.val

theorem standardSmoothDualPointsEquiv_unique (P : Algebra.SubmersivePresentation ℂ S ι σ)
    (x : S →ₐ[ℂ] ℂ) (u : ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ) (f : Dual.PresentedAlgebra.DualAlgebraPoints x)
    (hf : ∀ i : ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map, (f.val (P.val i.val)).snd = u i) :
    standardSmoothDualPointsEquiv P x u = f := by
  apply (standardSmoothDualPointsEquiv P x).symm.injective
  rw [Equiv.symm_apply_apply]
  funext i
  exact ((standardSmoothDualPointsEquiv_inverse P x f i).trans (hf i)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StandardSmoothDualCoordinates

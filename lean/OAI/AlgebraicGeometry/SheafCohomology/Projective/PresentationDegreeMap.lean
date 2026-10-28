import OAI.AlgebraicGeometry.SheafCohomology.Projective.PresentationPolynomialModule
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedCokernelDegree
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialMatrixComponents
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PresentedTargetCoordinates

/-! # Presentation Degree Map -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective

noncomputable section

open _root_.MvPolynomial

/-! Degree maps of the polynomial presentation and their actual degree cokernels. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
open OAI.AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation
variable {j : σ} {M : (Proj (homogeneousSubmodule σ R)).Modules}
    (D : TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation j M)

def TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.polynomialDegreeMap (n : ℕ) :
    HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading (σ := σ) Γ(Spec (CommRingCat.of R), ⊤)
      (fun k => (D.columnDegree k : ℤ)) (n : ℤ) →ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
    HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading (σ := σ) Γ(Spec (CommRingCat.of R), ⊤)
      (fun i => (D.rowDegree i : ℤ)) (n : ℤ) :=
  HilbertScheme.Presentations.Graded.Exactness.GradedModules.degreeMap _ _ (D.polynomialMap.restrictScalars Γ(Spec (CommRingCat.of R), ⊤))
    D.polynomialMap_homogeneous (n : ℤ)

theorem TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.polynomialDegreeMap_apply (n : ℕ)
    (x : HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading (σ := σ) Γ(Spec (CommRingCat.of R), ⊤)
      (fun k => (D.columnDegree k : ℤ)) (n : ℤ)) (i : Fin D.rows) :
    (D.polynomialDegreeMap n x).val i = ∑ k, (D.polynomialMatrix i k).val * x.val k := by
  change HomogeneousPolynomialMatrix.homogeneousPolynomialMatrixMap D.rowDegree D.columnDegree D.polynomialMatrix x.val i = _
  exact PolynomialMatrixComponents.homogeneousPolynomialMatrixMap_apply D.rowDegree D.columnDegree D.polynomialMatrix x.val i

def TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.polynomialDegreeCokernelEquiv (n : ℕ) :
    PresentedTargetCoordinates.LinearCokernel (R := Γ(Spec (CommRingCat.of R), ⊤))
      (M := ↥(HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading (σ := σ) Γ(Spec (CommRingCat.of R), ⊤)
        (fun k => (D.columnDegree k : ℤ)) (n : ℤ)))
      (N := ↥(HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading (σ := σ) Γ(Spec (CommRingCat.of R), ⊤)
        (fun i => (D.rowDegree i : ℤ)) (n : ℤ))) (D.polynomialDegreeMap n) ≃ₗ[
        Γ(Spec (CommRingCat.of R), ⊤)] D.DegreeCokernel (n : ℤ) :=
  GradedCokernelDegree.homogeneousDegreeCokernelEquiv _ _ D.polynomialMap D.polynomialMap_homogeneous (n : ℤ)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective

import OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexMinimalResolution
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PresentationGradedModule
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedQuotientLift

/-! # Complex Presentation Augmentation -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexPresentationAugmentation

noncomputable section

/-! The actual map from the minimal free sheaf to the original presented sheaf. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.MvPolynomial
namespace ComplexResolution
variable {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra ComplexMinimalResolution.ComplexResolution.complexResolutionField
variable {j : σ} {M : (Proj (homogeneousSubmodule σ ℂ)).Modules}
    (D : TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation j M)

def presentationLiftPolynomial :
    (Fin (GradedMinimalFiniteCover.augmentationRank D.gradedCokernel) →₀ MvPolynomial σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)) →ₗ[
      MvPolynomial σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)] (Fin D.rows →₀ MvPolynomial σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)) :=
  GradedQuotientLift.GradedQuotientMinimalLift.lift D.generatorModule D.polynomialMap.range
    D.polynomialRelations_homogeneous D.gradedCokernel_nonnegative

theorem presentationLiftPolynomial_homogeneous (n : ℤ)
    (x : Fin (GradedMinimalFiniteCover.augmentationRank D.gradedCokernel) →₀ MvPolynomial σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤))
    (hx : x ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)
      (fun i => (GradedMinimalFiniteCover.augmentationFinWeight D.gradedCokernel i : ℤ)) n) :
    presentationLiftPolynomial D x ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)
      (fun i => (D.rowDegree i : ℤ)) n :=
  GradedQuotientLift.GradedQuotientMinimalLift.lift_homogeneous D.generatorModule D.polynomialMap.range
    D.polynomialRelations_homogeneous D.gradedCokernel_nonnegative n x hx

theorem presentationLiftPolynomial_projection :
    D.polynomialMap.range.mkQ.comp (presentationLiftPolynomial D) =
      GradedMinimalFiniteCover.augmentationFinProjection D.gradedCokernel :=
  GradedQuotientLift.GradedQuotientMinimalLift.projection_comp_lift D.generatorModule D.polynomialMap.range
    D.polynomialRelations_homogeneous D.gradedCokernel_nonnegative

def presentationLift : ComplexMinimalResolution.ComplexResolution.freeSheaf j D.gradedCokernel ⟶
    ∐ fun i => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := ℂ) j (D.rowDegree i) :=
  GradedPolynomialMap.MvPolynomial.coordinateGradedPolynomialSheafMap (R := ℂ) j D.rowDegree
    (GradedMinimalFiniteCover.augmentationFinWeight D.gradedCokernel) (presentationLiftPolynomial D)
    (presentationLiftPolynomial_homogeneous D)

def presentationAugmentation : ComplexMinimalResolution.ComplexResolution.freeSheaf j D.gradedCokernel ⟶ M :=
  presentationLift D ≫ D.projection

end ComplexResolution

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexPresentationAugmentation

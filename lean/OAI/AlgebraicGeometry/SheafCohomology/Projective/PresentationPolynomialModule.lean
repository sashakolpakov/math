import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistPolynomialMatrix
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousPolynomialMatrix
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedModuleHilbertPolynomial

/-! # Presentation Polynomial Module -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective

noncomputable section

open _root_.MvPolynomial

/-! The graded polynomial presentation extracted from an actual coherent sheaf presentation. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

section
variable {j : σ} {M : (Proj (homogeneousSubmodule σ R)).Modules}
    (D : TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation j M)

def TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.polynomialMatrix (i : Fin D.rows) (k : Fin D.columns) :
    homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) (D.columnDegree k - D.rowDegree i) :=
  NegativeTwistPolynomialMatrix.MvPolynomial.coordinateNegativeTwistPolynomialMatrix j D.rowDegree D.columnDegree D.degree_order D.relations i k

def TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.polynomialMap :
    (Fin D.columns →₀ MvPolynomial σ Γ(Spec (CommRingCat.of R), ⊤)) →ₗ[
      MvPolynomial σ Γ(Spec (CommRingCat.of R), ⊤)]
      (Fin D.rows →₀ MvPolynomial σ Γ(Spec (CommRingCat.of R), ⊤)) :=
  HomogeneousPolynomialMatrix.homogeneousPolynomialMatrixMap D.rowDegree D.columnDegree D.polynomialMatrix

abbrev TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.generatorModule : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ Γ(Spec (CommRingCat.of R), ⊤) :=
  HomogeneousPolynomialMatrix.weightedFreePolynomialModule (fun i => (D.rowDegree i : ℤ))

theorem TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.polynomialMap_homogeneous (n : ℤ)
    (x : Fin D.columns →₀ MvPolynomial σ Γ(Spec (CommRingCat.of R), ⊤))
    (hx : x ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading Γ(Spec (CommRingCat.of R), ⊤)
      (fun k => (D.columnDegree k : ℤ)) n) :
    D.polynomialMap x ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading Γ(Spec (CommRingCat.of R), ⊤)
      (fun i => (D.rowDegree i : ℤ)) n :=
  HomogeneousPolynomialMatrix.homogeneousPolynomialMatrixMap_homogeneous D.rowDegree D.columnDegree
    D.degree_order D.polynomialMatrix n x hx

theorem TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.polynomialRelations_homogeneous : D.polynomialMap.range.IsHomogeneous
    (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading Γ(Spec (CommRingCat.of R), ⊤) (fun i => (D.rowDegree i : ℤ))) :=
  HomogeneousPolynomialMatrix.homogeneousPolynomialMatrixMap_range_isHomogeneous D.rowDegree D.columnDegree
    D.degree_order D.polynomialMatrix

abbrev TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.DegreeCokernel (n : ℤ) :=
  GradedCyclicDegreeSequence.DegreeQuotient
    (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading Γ(Spec (CommRingCat.of R), ⊤) (fun i => (D.rowDegree i : ℤ)))
    D.polynomialMap.range n

end

variable {r : ℕ} {j : Fin (r + 1)}
    {M : (Proj (homogeneousSubmodule (Fin (r + 1)) R)).Modules}
    (D : TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation j M)

theorem TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.degreeCokernel_eventuallyPolynomial (hfield : IsField Γ(Spec (CommRingCat.of R), ⊤)) :
    EventualPolynomial.EventuallyPolynomial (fun n =>
      (Module.finrank Γ(Spec (CommRingCat.of R), ⊤) (D.DegreeCokernel (n : ℤ)) : ℚ)) := by
  let := hfield.toField
  exact GradedModuleHilbertPolynomial.finiteGradedModule_quotient_eventuallyPolynomial D.generatorModule D.polynomialMap.range
    D.polynomialRelations_homogeneous

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective

import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ConcentrationHom

/-! # Cohomology Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.CohomologyMap.LocalSectionClass

noncomputable section

/-! The cohomology map and composition law used by the local point comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem replace_middle_last {D : Type*} [Category D]
    {A B C E F : D} {f : A ⟶ F} {a : A ⟶ B} {b : B ⟶ C}
    {c c' : C ⟶ E} {d d' : E ⟶ F}
    (h : f = a ≫ b ≫ c ≫ d) (hc : c' = c) (hd : d' = d) :
    f = (a ≫ b) ≫ (c' ≫ d') := by
  simpa only [hc, hd, Category.assoc] using h

universe u
variable {R : Type u} [CommRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cohomologyMap_coordinates (g : ℕ)
    {P Q : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Modules} (φ : P ⟶ Q) :
    (ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := Fin (n+2)) g).map φ =
      (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.forgetScalars (S := Spec (CommRingCat.of R))).map
        (homologyMap ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor
          (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))
          (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n+2)))).map φ) g) := by
  simp only [ProjectiveRefinement.Serre.cohomologyFunctor,
    Trace.PureFunctorNaturality.cohomologyFunctor, TopCechRightExact.functor,
    IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.forgetScalars, Functor.comp_map, homologyFunctor_map]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.CohomologyMap.LocalSectionClass

import OAI.AlgebraicGeometry.SheafCohomology.Projective.SectionsHilbertPolynomial
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleHilbertDegreeBound

/-! # Sections Hilbert Degree Bound -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective

noncomputable section

open _root_.MvPolynomial

/-! Ambient degree bounds for Hilbert polynomials of actual projective sections. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleHilbertDegreeBound
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {r : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

section
open OAI.AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation
variable {j : Fin (r + 1)} {M : (Proj (homogeneousSubmodule (Fin (r + 1)) R)).Modules}
    (D : TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation j M)

omit [IsNoetherianRing R] in
theorem TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.degreeCokernel_eventuallyPolynomialOfDegree
    (hfield : IsField Γ(Spec (CommRingCat.of R), ⊤)) :
    BoundedEventualPolynomial.EventuallyPolynomialOfDegree (fun n =>
      (Module.finrank Γ(Spec (CommRingCat.of R), ⊤) (D.DegreeCokernel (n : ℤ)) : ℚ)) r := by
  let := hfield.toField
  exact ModuleHilbertDegreeBound.finiteGradedModule_quotient_eventuallyPolynomialOfDegree
    D.generatorModule D.polynomialMap.range D.polynomialRelations_homogeneous

end

theorem SectionsHilbertDegreeBound.MvPolynomial.finiteType_projectiveTwist_sections_eventuallyPolynomialOfDegree
    (M : (Proj (homogeneousSubmodule (Fin (r + 1)) R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (j : Fin (r + 1))
    (hfield : IsField Γ(Spec (CommRingCat.of R), ⊤)) :
    BoundedEventualPolynomial.EventuallyPolynomialOfDegree (fun n =>
      (Module.finrank Γ(Spec (CommRingCat.of R), ⊤)
        ((AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (r + 1)))).obj
          ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.obj M)) : ℚ)) r := by
  obtain ⟨D⟩ := TwoStagePresentation.MvPolynomial.exists_coordinateNegativeTwistPresentation M j
  obtain ⟨P, hP, b, hb⟩ := D.degreeCokernel_eventuallyPolynomialOfDegree hfield
  obtain ⟨c, hc⟩ := D.eventually_degreeCokernel_sections
  refine ⟨P, hP, max b c, fun n hn => ?_⟩
  obtain ⟨e⟩ := hc n ((le_max_right b c).trans hn)
  have hdim := e.finrank_eq
  exact (congrArg (fun k : ℕ => (k : ℚ)) hdim).symm.trans
    (hb n ((le_max_left b c).trans hn))

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective

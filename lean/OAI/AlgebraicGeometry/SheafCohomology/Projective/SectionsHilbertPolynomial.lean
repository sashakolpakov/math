import OAI.AlgebraicGeometry.SheafCohomology.Projective.SectionPolynomialMap

/-! # Sections Hilbert Polynomial -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.SectionsHilbertPolynomial

noncomputable section

open _root_.MvPolynomial

/-! Hilbert polynomials of the actual global sections of coherent projective twists. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {r : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem finiteType_projectiveTwist_sections_eventuallyPolynomial
    (M : (Proj (homogeneousSubmodule (Fin (r + 1)) R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (j : Fin (r + 1))
    (hfield : IsField Γ(Spec (CommRingCat.of R), ⊤)) :
    EventualPolynomial.EventuallyPolynomial (fun n =>
      (Module.finrank Γ(Spec (CommRingCat.of R), ⊤)
        ((AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (r + 1)))).obj
          ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.obj M)) : ℚ)) := by
  obtain ⟨D⟩ := TwoStagePresentation.MvPolynomial.exists_coordinateNegativeTwistPresentation M j
  obtain ⟨P, b, hb⟩ := D.degreeCokernel_eventuallyPolynomial hfield
  obtain ⟨c, hc⟩ := D.eventually_degreeCokernel_sections
  refine ⟨P, max b c, fun n hn => ?_⟩
  obtain ⟨e⟩ := hc n ((le_max_right b c).trans hn)
  have hdim := e.finrank_eq
  exact (congrArg (fun k : ℕ => (k : ℚ)) hdim).symm.trans
    (hb n ((le_max_left b c).trans hn))

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.SectionsHilbertPolynomial

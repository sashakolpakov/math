import OAI.AlgebraicGeometry.SheafCohomology.Projective.SectionsHilbertDegreeBound
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedTwistSections

/-! # Closed Projective Hilbert -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ClosedProjectiveHilbert.Construction

noncomputable section

/-! Hilbert polynomials of actual sections on closed projective schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {r : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

local instance (X : Scheme.{u}) : MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

theorem closedProjective_sections_eventuallyPolynomial
    {X : Scheme.{u}} (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R))
    [IsClosedImmersion f] (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : Fin (r + 1)) (hfield : IsField Γ(Spec (.of R), ⊤)) :
    AlgebraicGeometry.SheafCohomology.Projective.BoundedEventualPolynomial.EventuallyPolynomialOfDegree (fun n =>
      (Module.finrank Γ(Spec (.of R), ⊤)
        ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ
          (R := R) (σ := Fin (r + 1)))).obj
          (M ⊗ (Scheme.Modules.pullback f).obj
            (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n))) : ℚ)) r := by
  let N := (Scheme.Modules.pushforward f).obj M
  have : N.IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f
  have : N.IsFiniteType := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_pushforward_of_isClosedImmersion f
  obtain ⟨P, hd, b, hb⟩ :=
    AlgebraicGeometry.SheafCohomology.Projective.SectionsHilbertDegreeBound.MvPolynomial.finiteType_projectiveTwist_sections_eventuallyPolynomialOfDegree N j hfield
  refine ⟨P, hd, b, fun n hn => ?_⟩
  let e := AlgebraicGeometry.SheafCohomology.Projective.ClosedTwistSections.MvPolynomial.closedImmersion_projectiveTwist_sectionsLinearEquiv f M j n
  exact (congrArg (fun k : ℕ => (k : ℚ)) e.finrank_eq).trans (hb n hn)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ClosedProjectiveHilbert.Construction

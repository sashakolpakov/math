import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveFilteredSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedTwistSections

/-! # Composite Pushforward Projective Sections -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CompositePushforwardProjectiveSections.Construction

noncomputable section

/-! The section space of a composite pushforward agrees with the intermediate pushforward's twisted sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

universe u

local instance compositePushforwardProjectiveSectionsMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def compositePushforwardProjectiveSectionsEquiv {X Z : Scheme.{u}}
    (f : X ⟶ Z) (a : Z ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion a]
    (j : σ) (n : ℕ) :
    (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
      ((Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) ⊗
        (Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n)) ≃ₗ[Γ(Spec (.of R), ⊤)]
    (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ).obj
      ((Scheme.Modules.pushforward (f ≫ a)).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) ⊗
        AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n) := by
  let O := AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X
  let P := AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n
  let e := (Scheme.Modules.pushforwardComp f a).app O
  let eT := MonoidalCategory.tensorIso e (Iso.refl P)
  exact (AlgebraicGeometry.SheafCohomology.Projective.ClosedTwistSections.MvPolynomial.closedImmersion_projectiveTwist_sectionsLinearEquiv a
    ((Scheme.Modules.pushforward f).obj O) j n).trans
      (((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ).mapIso eT).toLinearEquiv)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CompositePushforwardProjectiveSections.Construction

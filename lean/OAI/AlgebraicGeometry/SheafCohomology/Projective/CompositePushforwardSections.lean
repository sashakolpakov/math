import OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedTwistSections

/-! # Composite Pushforward Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.CompositePushforwardSections.Dimension

noncomputable section

/-! The section space of a composite pushforward agrees with the intermediate pushforward's twisted sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

universe u

local instance compositePushforwardProjectiveSectionsMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def compositePushforwardProjectiveSectionsEquiv {X Z : Scheme.{u}}
    (f : X ⟶ Z) (a : Z ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion a]
    (j : σ) (n : ℕ) :
    (AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
      ((Scheme.Modules.pushforward f).obj (Invertible.Scheme.Modules.unitObj X) ⊗
        (Scheme.Modules.pullback a).obj (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n)) ≃ₗ[Γ(Spec (.of R), ⊤)]
    (AdditiveCoproductSections.baseGlobalSectionsFunctor MvPolynomialClosure.MvPolynomial.homogeneousProjπ).obj
      ((Scheme.Modules.pushforward (f ≫ a)).obj (Invertible.Scheme.Modules.unitObj X) ⊗
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n) := by
  let O := Invertible.Scheme.Modules.unitObj X
  let P := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n
  let e := (Scheme.Modules.pushforwardComp f a).app O
  let eT := MonoidalCategory.tensorIso e (Iso.refl P)
  exact (ClosedTwistSections.MvPolynomial.closedImmersion_projectiveTwist_sectionsLinearEquiv a
    ((Scheme.Modules.pushforward f).obj O) j n).trans
      (((AdditiveCoproductSections.baseGlobalSectionsFunctor MvPolynomialClosure.MvPolynomial.homogeneousProjπ).mapIso eT).toLinearEquiv)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.CompositePushforwardSections.Dimension

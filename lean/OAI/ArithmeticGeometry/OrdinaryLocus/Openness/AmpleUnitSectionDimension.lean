import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.EmbeddedAmpleSectionDimension
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectivePolynomialQuotient

/-! # Ample Unit Section Dimension -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmpleUnitSectionDimension.Construction

noncomputable section

/-! The untensored projective twist has the original ample power's global-section dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

local instance embeddedAmpleUnitSectionDimensionMonoidal (X : Scheme.{0}) :
    MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

attribute [local instance] MvPolynomial.gradedAlgebra

theorem embeddedAmpleSection_finrank {X S : Scheme.{0}} [IsAffine S]
    (f : X ⟶ S) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (d r : ℕ)
    (a : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) Γ(S, ⊤)))
    (hb : a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = f ≫ S.toSpecΓ)
    (e : (Scheme.Modules.pullback a).obj
      (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := Γ(S, ⊤)) (0 : Fin (r + 1))).sheaf ≅
      (L.tensorPower d).sheaf) (n : ℕ) :
    Module.finrank Γ(Spec (.of Γ(S, ⊤)), ⊤)
      ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
        ((Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower 0 n))) =
    Module.finrank Γ(S, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj (L.tensorPower (n * d)).sheaf) := by
  let T := (Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower
    (R := Γ(S, ⊤)) 0 n)
  have h₀ := ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).mapIso
    (ProjectivePolynomialQuotient.Construction.structureModuleTensorLeftIso T)).toLinearEquiv.finrank_eq
  have h₁ := EmbeddedAmpleSectionDimension.Construction.embeddedAmpleTwistSection_finrank f L d r a hb e (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) n
  have h₂ := ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).mapIso
    (SheafTensor.Construction.sheafTensorUnitLeft (L.tensorPower (n * d)).sheaf)).toLinearEquiv.finrank_eq
  exact h₀.symm.trans (h₁.trans h₂)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmpleUnitSectionDimension.Construction

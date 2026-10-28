import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmpleHilbert
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveCoordinateBundleIso

/-! # Embedded Ample Section Dimension -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.EmbeddedAmpleSectionDimension.Construction

noncomputable section

/-! Projective twist dimensions agree with the chosen powers of the original ample bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

local instance embeddedAmpleSectionDimensionMonoidal (X : Scheme.{0}) :
    MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

attribute [local instance] MvPolynomial.gradedAlgebra

theorem embeddedAmpleTwistSection_finrank {X S : Scheme.{0}} [IsAffine S]
    (f : X ⟶ S) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (d r : ℕ)
    (a : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) Γ(S, ⊤)))
    (hb : a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = f ≫ S.toSpecΓ)
    (e : (Scheme.Modules.pullback a).obj
      (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := Γ(S, ⊤)) (0 : Fin (r + 1))).sheaf ≅
      (L.tensorPower d).sheaf) (M : X.Modules) (n : ℕ) :
    Module.finrank Γ(Spec (.of Γ(S, ⊤)), ⊤)
      ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
        (M ⊗ (Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower 0 n))) =
    Module.finrank Γ(S, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj
      (SheafTensor.Construction.sheafTensor M (L.tensorPower (n * d)).sheaf)) := by
  have : IsIso S.toSpecΓ.appTop := by
    rw [Scheme.toSpecΓ_appTop]
    infer_instance
  let T := (Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower
    (R := Γ(S, ⊤)) 0 n)
  let N := SheafTensor.Construction.sheafTensor M (L.tensorPower (n * d)).sheaf
  let eL : T ≅ (L.tensorPower (n * d)).sheaf :=
    ProjectiveTwistComparison.Construction.pullbackProjectiveTwistIso a 0 (L.tensorPower d) e n ≪≫ (L.tensorPowerComposeIso n d).symm
  let eN : M ⊗ T ≅ N := AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalTensorObjIso M T ≪≫ SheafTensor.Construction.sheafTensorCongr (Iso.refl M) eL
  exact (((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).mapIso eN).toLinearEquiv.finrank_eq).trans
    ((GlobalSectionDimension.Construction.baseGlobalSections_finrank_congr hb N).trans (GlobalSectionDimension.Construction.baseGlobalSections_finrank_comp f S.toSpecΓ N))

theorem projectiveTwistedSection_finrank_coordinate
    {R : Type} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ] {X : Scheme}
    (a : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) (M : X.Modules) (i j : σ) (n : ℕ) :
    Module.finrank Γ(Spec (.of R), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
      (M ⊗ (Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower i n))) =
    Module.finrank Γ(Spec (.of R), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
      (M ⊗ (Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n))) := by
  let e := (Scheme.Modules.pullback a).mapIso (ProjectiveCoordinateBundleIso.Construction.projectiveTwistCoordinateIso (R := R) i j n)
  exact (((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).mapIso
    (MonoidalCategory.tensorIso (Iso.refl M) e)).toLinearEquiv.finrank_eq)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.EmbeddedAmpleSectionDimension.Construction

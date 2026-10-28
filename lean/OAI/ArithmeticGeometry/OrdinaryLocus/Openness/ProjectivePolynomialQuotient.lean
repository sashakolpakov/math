import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ClosedImmersionModuleEpi
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProperSectionFiniteness
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsSurjective
import OAI.AlgebraicGeometry.SheafCohomology.Projective.DegreeZeroPolynomials
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedTwistSections

/-! # Projective Polynomial Quotient -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectivePolynomialQuotient.Construction

noncomputable section

/-! Sufficiently positive sections on a projective closed subscheme are quotients
of actual homogeneous polynomial spaces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

universe u

local instance projectivePolynomialQuotientMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

def structureModuleTensorLeftIso {X : Scheme.{u}} (M : X.Modules) :
    AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X ⊗ M ≅ M :=
  ((AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl M) ≪≫ λ_ M

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def projectivePolynomialStructureSectionsEquiv (j : σ) (n : ℕ) :
    MvPolynomial.homogeneousSubmodule σ Γ(Spec (.of R), ⊤) n ≃ₗ[Γ(Spec (.of R), ⊤)]
      (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
        (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (Proj (MvPolynomial.homogeneousSubmodule σ R)) ⊗
          AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n) :=
  (AlgebraicGeometry.SheafCohomology.Projective.DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j n).symm.trans
    (((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ).mapIso
      (structureModuleTensorLeftIso
        (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n))).toLinearEquiv.symm)

def closedProjectiveTwistSectionReductionEquiv {X : Scheme.{u}}
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (j : σ) (n : ℕ) :
    (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) ⊗
        AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
      ≃ₗ[Γ(Spec (.of R), ⊤)]
    (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
      ((Scheme.Modules.pullback f).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower
        (R := R) j n)) :=
  (AlgebraicGeometry.SheafCohomology.Projective.ClosedTwistSections.MvPolynomial.closedImmersion_projectiveTwist_sectionsLinearEquiv
    f (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) j n).symm.trans
    (((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).mapIso
      (structureModuleTensorLeftIso _)).toLinearEquiv)

def closedProjectivePolynomialSectionsMap {X : Scheme.{u}}
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (j : σ) (n : ℕ) :
    MvPolynomial.homogeneousSubmodule σ Γ(Spec (.of R), ⊤) n →ₗ[Γ(Spec (.of R), ⊤)]
      (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
        ((Scheme.Modules.pullback f).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower
          (R := R) j n)) :=
  (closedProjectiveTwistSectionReductionEquiv f j n).toLinearMap.comp
    ((((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ).map
      ((AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))).hom).comp
          (projectivePolynomialStructureSectionsEquiv (R := R) j n).toLinearMap)

theorem closedProjectivePolynomialSectionsMap_eventually_surjective
    [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion f] (j : σ) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → Function.Surjective (closedProjectivePolynomialSectionsMap f j n) := by
  let Y := Proj (MvPolynomial.homogeneousSubmodule σ R)
  have : (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y).IsQuasicoherent :=
    LineBundleQuasicoherent.Construction.isQuasicoherent_of_isLineBundle _ (LineBundle.Construction.isLineBundle_structureSheaf Y)
  have : (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y).IsFiniteType :=
    ProjectiveCohomologyFiniteness.Construction.isFiniteType_of_isLineBundle _ (LineBundle.Construction.isLineBundle_structureSheaf Y)
  have : (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X).IsQuasicoherent :=
    LineBundleQuasicoherent.Construction.isQuasicoherent_of_isLineBundle _ (LineBundle.Construction.isLineBundle_structureSheaf X)
  have : ((Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom _
  let q : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y ⟶
      (Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have : Epi q := ClosedImmersionModuleEpi.Construction.closedImmersion_structureModule_epi f
  obtain ⟨b, hb⟩ := AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsSurjective.MvPolynomial.finiteType_epi_eventually_projectiveTwist_sections_surjective
    (M := AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y)
    (N := (Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)) q j
  refine ⟨b, fun n hn => ?_⟩
  exact (closedProjectiveTwistSectionReductionEquiv f j n).surjective.comp
    ((hb n hn).comp (projectivePolynomialStructureSectionsEquiv (R := R) j n).surjective)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectivePolynomialQuotient.Construction

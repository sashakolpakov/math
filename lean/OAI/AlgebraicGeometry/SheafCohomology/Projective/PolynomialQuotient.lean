import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ClosedImmersionModuleEpi
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleQuasicoherent
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsSurjective
import OAI.AlgebraicGeometry.SheafCohomology.Projective.DegreeZeroPolynomials
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedTwistSections

/-! # Polynomial Quotient -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialQuotient.Dimension

noncomputable section

/-! Sufficiently positive sections on a projective closed subscheme are quotients
of actual homogeneous polynomial spaces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

universe u

/-- Finite local trivializations give actual finite-type module sheaves. -/
theorem isFiniteType_of_isLineBundle {X : Scheme.{u}} (M : X.Modules)
    (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) : M.IsFiniteType := by
  have : M.IsFinitePresentation := ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleQuasicoherent.Construction.isFinitePresentation_of_isLineBundle M hM
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  refine { exists_localGeneratorsData := ⟨q.localGeneratorsData, ?_⟩ }
  constructor
  intro i
  exact (hq.isFinite_presentation i).isFiniteType_generators

local instance projectivePolynomialQuotientMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Monoidal.Scheme.Modules.monoidalCategory X

def structureModuleTensorLeftIso {X : Scheme.{u}} (M : X.Modules) :
    Invertible.Scheme.Modules.unitObj X ⊗ M ≅ M :=
  ((TensorSections.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl M) ≪≫ λ_ M

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def projectivePolynomialStructureSectionsEquiv (j : σ) (n : ℕ) :
    MvPolynomial.homogeneousSubmodule σ Γ(Spec (.of R), ⊤) n ≃ₗ[Γ(Spec (.of R), ⊤)]
      (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
        (Invertible.Scheme.Modules.unitObj (Proj (MvPolynomial.homogeneousSubmodule σ R)) ⊗
          TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n) :=
  (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j n).symm.trans
    (((AdditiveCoproductSections.baseGlobalSectionsFunctor MvPolynomialClosure.MvPolynomial.homogeneousProjπ).mapIso
      (structureModuleTensorLeftIso
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n))).toLinearEquiv.symm)

def closedProjectiveTwistSectionReductionEquiv {X : Scheme.{u}}
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (j : σ) (n : ℕ) :
    (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((Scheme.Modules.pushforward f).obj (Invertible.Scheme.Modules.unitObj X) ⊗
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
      ≃ₗ[Γ(Spec (.of R), ⊤)]
    (AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
      ((Scheme.Modules.pullback f).obj (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower
        (R := R) j n)) :=
  (ClosedTwistSections.MvPolynomial.closedImmersion_projectiveTwist_sectionsLinearEquiv
    f (Invertible.Scheme.Modules.unitObj X) j n).symm.trans
    (((AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).mapIso
      (structureModuleTensorLeftIso _)).toLinearEquiv)

def closedProjectivePolynomialSectionsMap {X : Scheme.{u}}
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (j : σ) (n : ℕ) :
    MvPolynomial.homogeneousSubmodule σ Γ(Spec (.of R), ⊤) n →ₗ[Γ(Spec (.of R), ⊤)]
      (AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
        ((Scheme.Modules.pullback f).obj (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower
          (R := R) j n)) :=
  (closedProjectiveTwistSectionReductionEquiv f j n).toLinearMap.comp
    ((((AdditiveCoproductSections.baseGlobalSectionsFunctor MvPolynomialClosure.MvPolynomial.homogeneousProjπ).map
      ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))).hom).comp
          (projectivePolynomialStructureSectionsEquiv (R := R) j n).toLinearMap)

theorem closedProjectivePolynomialSectionsMap_eventually_surjective
    [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion f] (j : σ) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → Function.Surjective (closedProjectivePolynomialSectionsMap f j n) := by
  let Y := Proj (MvPolynomial.homogeneousSubmodule σ R)
  have : (Invertible.Scheme.Modules.unitObj Y).IsQuasicoherent :=
    ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleQuasicoherent.Construction.isQuasicoherent_of_isLineBundle _ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_structureSheaf Y)
  have : (Invertible.Scheme.Modules.unitObj Y).IsFiniteType :=
    isFiniteType_of_isLineBundle _ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_structureSheaf Y)
  have : (Invertible.Scheme.Modules.unitObj X).IsQuasicoherent :=
    ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleQuasicoherent.Construction.isQuasicoherent_of_isLineBundle _ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_structureSheaf X)
  have : ((Scheme.Modules.pushforward f).obj (Invertible.Scheme.Modules.unitObj X)).IsQuasicoherent :=
    Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom _
  let q : Invertible.Scheme.Modules.unitObj Y ⟶
      (Scheme.Modules.pushforward f).obj (Invertible.Scheme.Modules.unitObj X) :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have : Epi q := ArithmeticGeometry.OrdinaryLocus.Openness.ClosedImmersionModuleEpi.Construction.closedImmersion_structureModule_epi f
  obtain ⟨b, hb⟩ := GlobalSectionsSurjective.MvPolynomial.finiteType_epi_eventually_projectiveTwist_sections_surjective
    (M := Invertible.Scheme.Modules.unitObj Y)
    (N := (Scheme.Modules.pushforward f).obj (Invertible.Scheme.Modules.unitObj X)) q j
  refine ⟨b, fun n hn => ?_⟩
  exact (closedProjectiveTwistSectionReductionEquiv f j n).surjective.comp
    ((hb n hn).comp (projectivePolynomialStructureSectionsEquiv (R := R) j n).surjective)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialQuotient.Dimension

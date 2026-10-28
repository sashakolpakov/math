import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveNormalizedSections
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardOpenSections
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.HomogeneousFilteredImage
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveTwistComparison

/-! # Projective Filtered Sections -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveFilteredSections.Construction

noncomputable section

/-! Sufficiently positive actual projective sections are the degree filtration of an affine chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

universe u

local instance projectiveFilteredSectionsMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def closedProjectiveChartCoordinates {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) :
    σ → Γ(X, f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) := fun i => ProjectiveChartScalars.Construction.closedProjectiveChartPolynomialAlgHom f j (MvPolynomial.X i)

omit [LinearOrder σ] in
theorem closedProjectiveChartCoordinates_anchor {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) :
    closedProjectiveChartCoordinates f j j = 1 := by
  change f.app (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) (ProjectiveChartPolynomialMap.Construction.projectiveChartPolynomialMap j (MvPolynomial.X j)) = 1
  rw [ProjectiveChartPolynomialMap.Construction.projectiveChartPolynomialMap_anchor, map_one]

def closedProjectiveNormalizedSectionMap {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ) :
    letI := BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
    (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) ⊗
        AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n) →ₗ[Γ(Spec (.of R), ⊤)]
      Γ(X, f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) :=
  letI := BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  (PushforwardOpenSections.Construction.pushforwardUnitOpenSectionsLinearEquiv f AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)).toLinearMap.comp
    (BaseOpenSections.Construction.tensorSectionGlobalCoefficientLinear AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ
      ((Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X))
      (ProjectiveNormalizedSections.Construction.projectiveTwistUnitSection j n) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j))

omit [Fintype σ] [LinearOrder σ] in
theorem closedProjectiveNormalizedSectionMap_injective {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ)
    [Nonempty (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)] :
    Function.Injective (closedProjectiveNormalizedSectionMap f j n) := by
  apply (PushforwardOpenSections.Construction.pushforwardUnitOpenSectionsLinearEquiv f AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)).injective.comp
  apply TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient_injective
  apply TensorSectionRestriction.Construction.tensorPushforward_lineBundle_section_restriction_injective f
  exact LineBundle.Construction.isLineBundle_of_iso (ProjectiveTwistComparison.Construction.projectiveTwistTensorPowerIso j n).symm
    (TensorRestriction.Construction.isLineBundle_sheafTensorPower (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) j).locallyTrivial n)

def closedProjectiveFilteredSectionsEquiv {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ)
    [Nonempty (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)]
    (hq : Function.Surjective (ProjectiveNormalizedSections.Construction.closedProjectiveAmbientPolynomialSectionsMap f j n)) :
    letI := BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
    (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) ⊗
        AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n) ≃ₗ[Γ(Spec (.of R), ⊤)]
      PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := Γ(Spec (.of R), ⊤)) (closedProjectiveChartCoordinates f j) n := by
  letI := BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  apply HomogeneousFilteredImage.Construction.homogeneousQuotientFilteredEquiv (closedProjectiveChartCoordinates f j) j
    (closedProjectiveChartCoordinates_anchor f j) n
    (ProjectiveNormalizedSections.Construction.closedProjectiveAmbientPolynomialSectionsMap f j n) hq
    (closedProjectiveNormalizedSectionMap f j n) (closedProjectiveNormalizedSectionMap_injective f j n)
  intro p
  exact (ProjectiveNormalizedSections.Construction.closedProjectiveAmbientPolynomialSectionsMap_coefficient f j n p).trans
    (AlgHom.congr_fun (MvPolynomial.aeval_unique (ProjectiveChartScalars.Construction.closedProjectiveChartPolynomialAlgHom f j)) p.val)

theorem closedProjective_sections_filtered_finrank [IsNoetherianRing R]
    (hfield : IsField Γ(Spec (.of R), ⊤)) {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f] (j : σ)
    [Nonempty (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)] :
    letI := BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      Module.finrank Γ(Spec (.of R), ⊤)
        ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
          ((Scheme.Modules.pullback f).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n))) =
      Module.finrank Γ(Spec (.of R), ⊤)
        (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := Γ(Spec (.of R), ⊤)) (closedProjectiveChartCoordinates f j) n) := by
  let := hfield.toField
  let := BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  obtain ⟨b, hb⟩ := ProjectiveNormalizedSections.Construction.closedProjectiveAmbientPolynomialSectionsMap_eventually_surjective f j
  refine ⟨b, fun n hn => ?_⟩
  exact (ProjectivePolynomialQuotient.Construction.closedProjectiveTwistSectionReductionEquiv f j n).finrank_eq.symm.trans
    (closedProjectiveFilteredSectionsEquiv f j n (hb n hn)).finrank_eq

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveFilteredSections.Construction

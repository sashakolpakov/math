import OAI.AlgebraicGeometry.SheafCohomology.Projective.NormalizedSections
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardOpenSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousQuotientFiltration
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers

/-! # Filtered Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredSections.Dimension

noncomputable section

/-! Sufficiently positive actual projective sections are the degree filtration of an affine chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardOpenSections.Construction

universe u

local instance projectiveFilteredSectionsMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def closedProjectiveChartCoordinates {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) :
    σ → Γ(X, f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j) := fun i => ChartScalars.Dimension.closedProjectiveChartPolynomialAlgHom f j (MvPolynomial.X i)

omit [LinearOrder σ] in
theorem closedProjectiveChartCoordinates_anchor {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) :
    closedProjectiveChartCoordinates f j j = 1 := by
  change f.app (MvPolynomialClosure.MvPolynomial.coordinateOpen j) (ChartPolynomialMap.Dimension.projectiveChartPolynomialMap j (MvPolynomial.X j)) = 1
  rw [ChartPolynomialMap.Dimension.projectiveChartPolynomialMap_anchor, map_one]

def closedProjectiveNormalizedSectionMap {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ) :
    letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j)
    (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((Scheme.Modules.pushforward f).obj (Invertible.Scheme.Modules.unitObj X) ⊗
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n) →ₗ[Γ(Spec (.of R), ⊤)]
      Γ(X, f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j) :=
  letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  (ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardOpenSections.Construction.pushforwardUnitOpenSectionsLinearEquiv f MvPolynomialClosure.MvPolynomial.homogeneousProjπ (MvPolynomialClosure.MvPolynomial.coordinateOpen j)).toLinearMap.comp
    (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.tensorSectionGlobalCoefficientLinear MvPolynomialClosure.MvPolynomial.homogeneousProjπ
      ((Scheme.Modules.pushforward f).obj (Invertible.Scheme.Modules.unitObj X))
      (UnitSection.Dimension.projectiveTwistUnitSection j n) (MvPolynomialClosure.MvPolynomial.coordinateOpen j))

omit [Fintype σ] [LinearOrder σ] in
theorem closedProjectiveNormalizedSectionMap_injective {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ)
    [Nonempty (f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j)] :
    Function.Injective (closedProjectiveNormalizedSectionMap f j n) := by
  apply (ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardOpenSections.Construction.pushforwardUnitOpenSectionsLinearEquiv f MvPolynomialClosure.MvPolynomial.homogeneousProjπ (MvPolynomialClosure.MvPolynomial.coordinateOpen j)).injective.comp
  apply ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient_injective
  apply ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionRestriction.Construction.tensorPushforward_lineBundle_section_restriction_injective f
  intro x
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ ⨆ i : σ, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i by
      rw [MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]; trivial)
  exact ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen i, hi, ⟨((Scheme.Modules.restrictFunctorIsoPullback
    (MvPolynomialClosure.MvPolynomial.coordinateOpen i).ι).app (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n)).symm ≪≫
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivialization i j n⟩⟩

def closedProjectiveFilteredSectionsEquiv {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ)
    [Nonempty (f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j)]
    (hq : Function.Surjective (PolynomialSectionMapDefs.Dimension.closedProjectiveAmbientPolynomialSectionsMap f j n)) :
    letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j)
    (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((Scheme.Modules.pushforward f).obj (Invertible.Scheme.Modules.unitObj X) ⊗
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n) ≃ₗ[Γ(Spec (.of R), ⊤)]
      PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := Γ(Spec (.of R), ⊤)) (closedProjectiveChartCoordinates f j) n := by
  letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  apply HomogeneousQuotientFiltration.Dimension.homogeneousQuotientFilteredEquiv (closedProjectiveChartCoordinates f j) j
    (closedProjectiveChartCoordinates_anchor f j) n
    (PolynomialSectionMapDefs.Dimension.closedProjectiveAmbientPolynomialSectionsMap f j n) hq
    (closedProjectiveNormalizedSectionMap f j n) (closedProjectiveNormalizedSectionMap_injective f j n)
  intro p
  exact (NormalizedSections.Dimension.closedProjectiveAmbientPolynomialSectionsMap_coefficient f j n p).trans
    (AlgHom.congr_fun (MvPolynomial.aeval_unique (ChartScalars.Dimension.closedProjectiveChartPolynomialAlgHom f j)) p.val)

theorem closedProjective_sections_filtered_finrank [IsNoetherianRing R]
    (hfield : IsField Γ(Spec (.of R), ⊤)) {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f] (j : σ)
    [Nonempty (f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j)] :
    letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j)
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      Module.finrank Γ(Spec (.of R), ⊤)
        ((AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
          ((Scheme.Modules.pullback f).obj (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n))) =
      Module.finrank Γ(Spec (.of R), ⊤)
        (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := Γ(Spec (.of R), ⊤)) (closedProjectiveChartCoordinates f j) n) := by
  let := hfield.toField
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  obtain ⟨b, hb⟩ := PolynomialSectionMap.Dimension.closedProjectiveAmbientPolynomialSectionsMap_eventually_surjective f j
  refine ⟨b, fun n hn => ?_⟩
  exact (PolynomialQuotient.Dimension.closedProjectiveTwistSectionReductionEquiv f j n).finrank_eq.symm.trans
    (closedProjectiveFilteredSectionsEquiv f j n (hb n hn)).finrank_eq

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredSections.Dimension

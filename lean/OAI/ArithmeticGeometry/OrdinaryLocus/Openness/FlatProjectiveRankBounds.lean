import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FactoredProjectiveModuleFiltration
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.WeightedSectionRankBounds
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectivePushforwardCoefficientInjective

/-! # Flat Projective Rank Bounds -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FlatProjectiveRankBounds.Construction

noncomputable section

/-! Actual sections of a finite flat pushforward satisfy shifted affine-filtration bounds of the scheme's rank. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

universe u

local instance finiteFlatProjectiveRankBoundsMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
    {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem finiteFlatProjective_sections_filtered_rank_bounds
    (hfield : IsField Γ(Spec (.of R), ⊤)) {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [IsFinite f] [Flat f]
    (a : Z ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion a] (j : σ)
    [Nonempty (a ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)] [Nonempty ((f ≫ a) ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)] :
    letI := BaseOpenSections.Construction.baseOpenSectionsAlgebra (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (a ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
    let D := f.finrank (((AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen (R := R) j).preimage a).fromSpec
      (⊥ : PrimeSpectrum Γ(Z, a ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)))
    let N := (Scheme.Modules.pushforward (f ≫ a)).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)
    ∃ b s : ℕ,
      (∀ n, b ≤ n → D * Module.finrank Γ(Spec (.of R), ⊤)
        (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := Γ(Spec (.of R), ⊤)) (ProjectiveFilteredSections.Construction.closedProjectiveChartCoordinates a j) n) ≤
          Module.finrank Γ(Spec (.of R), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ).obj
            (N ⊗ AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j (n + s)))) ∧
      (∀ n, b ≤ n → Module.finrank Γ(Spec (.of R), ⊤)
        ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ).obj (N ⊗ AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n)) ≤
          D * Module.finrank Γ(Spec (.of R), ⊤)
            (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := Γ(Spec (.of R), ⊤))
              (ProjectiveFilteredSections.Construction.closedProjectiveChartCoordinates a j) (n + s))) := by
  let := hfield.toField
  let π := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let U := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
  let B := Γ(Z, a ⁻¹ᵁ U)
  let N := (Scheme.Modules.pushforward (f ≫ a)).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)
  let M := (BaseOpenSections.Construction.baseOpenSectionsFunctor π U).obj N
  let := BaseOpenSections.Construction.baseOpenSectionsAlgebra (a ≫ π) (a ⁻¹ᵁ U)
  let := FactoredPushforwardOpenModule.Construction.factoredPushforwardOpenModule f a π U
  let := FactoredPushforwardOpenModule.Construction.factoredPushforwardOpenModule_tower f a π U
  let φ := ProjectiveChartScalars.Construction.closedProjectiveChartPolynomialAlgHom a j
  have hφ : Function.Surjective φ := ProjectiveChartScalars.Construction.closedProjectiveChartPolynomialAlgHom_surjective a j
  have : Algebra.FiniteType Γ(Spec (.of R), ⊤) B := Algebra.FiniteType.of_surjective φ hφ
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing Γ(Spec (.of R), ⊤) B
  have hU := (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen (R := R) j).preimage a
  have : Module.Flat B M := FiniteFlatChartModule.Construction.affinePreimageSectionModule_flat f (a ⁻¹ᵁ U) hU
  have : Module.FinitePresentation B M := FiniteFlatChartModule.Construction.affinePreimageSectionModule_finitePresentation f (a ⁻¹ᵁ U) hU
  have hv : Algebra.adjoin Γ(Spec (.of R), ⊤) (Set.range (ProjectiveFilteredSections.Construction.closedProjectiveChartCoordinates a j)) = ⊤ :=
    HomogeneousFilteredImage.Construction.adjoin_polynomial_generators_of_surjective φ hφ
  obtain ⟨r, w, d, b, hw, hb⟩ := FactoredProjectiveModuleFiltration.Construction.factoredProjective_normalized_image_eventually_weighted hfield f a j
  let E := fun n => (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor π).obj (N ⊗ AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n)
  let c := fun n => BaseOpenSections.Construction.tensorSectionGlobalCoefficientLinear π N (ProjectiveNormalizedSections.Construction.projectiveTwistUnitSection j n) U
  have hc (n : ℕ) : Function.Injective (c n) :=
    ProjectivePushforwardCoefficientInjective.Construction.projectivePushforwardCoefficientLinear_injective (f ≫ a) j n
  obtain ⟨s, hlo, hhi⟩ := WeightedSectionRankBounds.Construction.weightedSection_rank_shift_bounds
    (ProjectiveFilteredSections.Construction.closedProjectiveChartCoordinates a j) hv w hw d (fun n => ↥(E n)) c hc b hb
  have hrank : Module.rankAtStalk (R := B) M (⊥ : PrimeSpectrum B) =
      f.finrank (hU.fromSpec (⊥ : PrimeSpectrum B)) :=
    FiniteFlatChartModule.Construction.affinePreimageSectionModule_rank f (a ⁻¹ᵁ U) hU ⊥
  exact ⟨b, s, fun n hn => (hrank ▸ hlo n hn), fun n hn => (hrank ▸ hhi n hn)⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FlatProjectiveRankBounds.Construction

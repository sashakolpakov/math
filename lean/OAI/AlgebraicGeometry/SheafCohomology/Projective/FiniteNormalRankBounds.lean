import OAI.AlgebraicGeometry.SheafCohomology.Projective.FactoredModuleFiltration
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FreeFilteredRankBounds
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NormalAffineGenericRank
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PushforwardCoefficientInjective

/-! # Finite Normal Rank Bounds -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteNormalRankBounds.Dimension

noncomputable section

/-! Finite dominant maps from normal schemes have section-growth bounds of their actual function-field degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

universe u
local instance finiteNormalProjectiveRankBoundsMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
    {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem finiteNormalProjective_sections_filtered_rank_bounds
    (hfield : IsField Γ(Spec (.of R), ⊤)) {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [IsFinite f] [IsDominant f]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (a : Z ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion a] (j : σ)
    [Nonempty (a ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j)] [Nonempty ((f ≫ a) ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j)] :
    letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (a ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (a ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j)
    letI := DominantFunctionField.Dimension.dominantFunctionFieldAlgebra f
    let D := Module.finrank Z.functionField X.functionField
    let N := (Scheme.Modules.pushforward (f ≫ a)).obj (Invertible.Scheme.Modules.unitObj X)
    ∃ b s : ℕ,
      (∀ n, b ≤ n → D * Module.finrank Γ(Spec (.of R), ⊤)
        (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := Γ(Spec (.of R), ⊤)) (FilteredSections.Dimension.closedProjectiveChartCoordinates a j) n) ≤
          Module.finrank Γ(Spec (.of R), ⊤) ((AdditiveCoproductSections.baseGlobalSectionsFunctor MvPolynomialClosure.MvPolynomial.homogeneousProjπ).obj
            (N ⊗ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j (n + s)))) ∧
      (∀ n, b ≤ n → Module.finrank Γ(Spec (.of R), ⊤)
        ((AdditiveCoproductSections.baseGlobalSectionsFunctor MvPolynomialClosure.MvPolynomial.homogeneousProjπ).obj (N ⊗ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n)) ≤
          D * Module.finrank Γ(Spec (.of R), ⊤)
            (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := Γ(Spec (.of R), ⊤))
              (FilteredSections.Dimension.closedProjectiveChartCoordinates a j) (n + s))) := by
  let := hfield.toField
  let π := MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let U := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
  have : Nonempty (f ⁻¹ᵁ (a ⁻¹ᵁ U)) :=
    inferInstanceAs (Nonempty ((f ≫ a) ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen j))
  let B := Γ(Z, a ⁻¹ᵁ U)
  let N := (Scheme.Modules.pushforward (f ≫ a)).obj (Invertible.Scheme.Modules.unitObj X)
  let M := (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsFunctor π U).obj N
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (a ≫ π) (a ⁻¹ᵁ U)
  let := FactoredPushforwardOpenModule.Dimension.factoredPushforwardOpenModule f a π U
  let := FactoredPushforwardOpenModule.Dimension.factoredPushforwardOpenModule_tower f a π U
  let := DominantFunctionField.Dimension.dominantFunctionFieldAlgebra f
  let φ := ChartScalars.Dimension.closedProjectiveChartPolynomialAlgHom a j
  have hφ : Function.Surjective φ := ChartScalars.Dimension.closedProjectiveChartPolynomialAlgHom_surjective a j
  have : Algebra.FiniteType Γ(Spec (.of R), ⊤) B := Algebra.FiniteType.of_surjective φ hφ
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing Γ(Spec (.of R), ⊤) B
  have hU := (MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen (R := R) j).preimage a
  have : Module.IsTorsionFree B M := NormalAffineGenericRank.Dimension.affinePreimageSectionModule_torsionFree f (a ⁻¹ᵁ U)
  have : Module.FinitePresentation B M := FiniteFlatChartModule.Dimension.affinePreimageSectionModule_finitePresentation f (a ⁻¹ᵁ U) hU
  have : IsFractionRing B Z.functionField := functionField_isFractionRing_of_isAffineOpen Z (a ⁻¹ᵁ U) hU
  have hv : Algebra.adjoin Γ(Spec (.of R), ⊤) (Set.range (FilteredSections.Dimension.closedProjectiveChartCoordinates a j)) = ⊤ :=
    HomogeneousQuotientFiltration.Dimension.adjoin_polynomial_generators_of_surjective φ hφ
  obtain ⟨r, w, d, b, hw, hb⟩ := FactoredModuleFiltration.Dimension.factoredProjective_normalized_image_eventually_weighted hfield f a j
  let E := fun n => (AdditiveCoproductSections.baseGlobalSectionsFunctor π).obj (N ⊗ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n)
  let c := fun n => ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.tensorSectionGlobalCoefficientLinear π N (UnitSection.Dimension.projectiveTwistUnitSection j n) U
  have hc (n : ℕ) : Function.Injective (c n) :=
    PushforwardCoefficientInjective.Dimension.projectivePushforwardCoefficientLinear_injective (f ≫ a) j n
  obtain ⟨s, hlo, hhi⟩ := FreeFilteredRankBounds.Dimension.weightedTorsionFreeSection_rank_shift_bounds Z.functionField
    (FilteredSections.Dimension.closedProjectiveChartCoordinates a j) hv w hw d (fun n => ↥(E n)) c hc b hb
  have hrank := NormalAffineGenericRank.Dimension.affinePreimageSectionModule_genericRank f hX (a ⁻¹ᵁ U) hU
  exact ⟨b, s, fun n hn => (hrank ▸ hlo n hn), fun n hn => (hrank ▸ hhi n hn)⟩

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteNormalRankBounds.Dimension

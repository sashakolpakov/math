import OAI.NumberTheory.PadicHodge.GeometricComparison.DVR
import OAI.NumberTheory.PadicHodge.GeometricComparison.AbelianCrystallineAdapter
import OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearCharpolyTo
import OAI.AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators

/-! # Good -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The full repaired Cohomology proposition as an explicit input for the actual p-adic model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators
open scoped TensorProduct

universe u

/-- The complete good-reduction comparison proposition, without using its unproved theorem. -/
def Cohomology.Good.GoodReductionInput : Prop :=
  ∀
    (p : ℕ) [Fact p.Prime]
    (B : AlgebraicGeometry.Crystalline.Cohomology.Foundations.MixedCharacteristicDVR.{u} p)
    (X : Over (Spec (CommRingCat.of B.R)))
    [Smooth X.hom] [IsProper X.hom]
    (n : ℕ),
    ∃ cmp :
        (B.K ⊗[B.K₀] AlgebraicGeometry.Crystalline.Cohomology.Foundations.rationalCrystalline B X n) ≃ₗ[B.K]
          AlgebraicGeometry.Crystalline.Cohomology.Foundations.algebraicDeRham B X n,
      FiniteDimensional B.K₀ (AlgebraicGeometry.Crystalline.Cohomology.Foundations.rationalCrystalline B X n) ∧
      FiniteDimensional B.K (AlgebraicGeometry.Crystalline.Cohomology.Foundations.algebraicDeRham B X n) ∧
      Function.Bijective (AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.crystallineFrobenius B X n) ∧
      (∀ f : X ⟶ X,
        (∀ z, cmp ((AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.crystallinePullback B f n).baseChange B.K z) =
          AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.deRhamPullback B f n (cmp z)) ∧
        (∀ z, AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.crystallineFrobenius B X n (AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.crystallinePullback B f n z) =
          AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.crystallinePullback B f n (AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.crystallineFrobenius B X n z)) ∧
        (∀ j : ℤ, (AlgebraicGeometry.Crystalline.Cohomology.Foundations.hodgeFiltration B X n j).map (AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.deRhamPullback B f n) ≤
          AlgebraicGeometry.Crystalline.Cohomology.Foundations.hodgeFiltration B X n j)) ∧
      Antitone (fun j : ℤ =>
        (AlgebraicGeometry.Crystalline.Cohomology.Foundations.hodgeFiltration B X n j).comap cmp.toLinearMap) ∧
      (∀ j : ℤ, ((AlgebraicGeometry.Crystalline.Cohomology.Foundations.hodgeFiltration B X n j).comap cmp.toLinearMap).map cmp.toLinearMap =
        AlgebraicGeometry.Crystalline.Cohomology.Foundations.hodgeFiltration B X n j)

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.smallCrystalline_finite_of_Cohomology (hCohomology : Cohomology.Good.GoodReductionInput.{0}) :
    FiniteDimensional (FractionRing (GeometricComparison.Crystalline.CoefficientAdapter.Witt q)) A.SmallCrystalline := by
  obtain ⟨_, hfin, _⟩ := hCohomology q (DVR.PadicBase.dvr q) A.integral.scheme 1
  change FiniteDimensional (FractionRing (GeometricComparison.Crystalline.CoefficientAdapter.Witt q))
    (AlgebraicGeometry.Crystalline.Cohomology.Site.rationalCohomology q (ZMod q)
      ((DVR.PadicBase.dvr q).specialFiber A.integral.scheme) 1) at hfin
  rw [DVR.PadicBase.specialFiber_eq] at hfin
  exact hfin

theorem Geometry.AbelianH1Model.crystalline_finite_of_Cohomology (hCohomology : Cohomology.Good.GoodReductionInput.{0}) :
    FiniteDimensional ℚ_[q] A.Crystalline := by
  let : FiniteDimensional (FractionRing (GeometricComparison.Crystalline.CoefficientAdapter.Witt q)) A.SmallCrystalline :=
    A.smallCrystalline_finite_of_Cohomology hCohomology
  exact SemilinearCharpolyTo.SemilinearCharpoly.finite (GeometricComparison.Crystalline.CoefficientAdapter.coefficientFieldEquiv q) A.smallCrystallineEquiv

end

end OAI.NumberTheory.PadicHodge.GeometricComparison

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.FamiliesAtParameterPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.EmbeddedBaseChange

/-! # Closed Family Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual coefficient base change preserves flat closed Hilbert families in the bounded parameter construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R A : CommRingCat.{u}} [IsNoetherianRing R] [IsNoetherianRing A]
variable {n B N : ℕ} {P : Polynomial ℚ}
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
variable (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (htest : Truncated.PolynomialTest.truncatedHilbertTestBound n N ≤ B)
variable (hr : Generated.RankTests.GeneratedHilbertRankTest n P N)

def Flat.ClosedFamilies.FlatClosedHilbertFamily.coefficientBaseChange (F : Flat.ClosedFamilies.FlatClosedHilbertFamily R n P) (φ : R ⟶ A) :
    Flat.ClosedFamilies.FlatClosedHilbertFamily A n P := by
  let x := Flat.ClosedParameterEquivalence.flatClosedHilbertAffinePointEquiv hN hflat htest hr (𝟙 (Spec R)) F
  let y : Over.mk (Spec.map φ) ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters (Spec R) n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N :=
    (Over.homMk (Spec.map φ) (Category.comp_id _) : Over.mk (Spec.map φ) ⟶ Over.mk (𝟙 (Spec R))) ≫ x
  let G := Hilbert.FamiliesAtParameterPoints.hilbertFamilyAtParameterPoint hN hflat htest hr (Spec.map φ) y
  let C := F.val.pullbackAlong (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n) (Spec.map φ) (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback φ n)
  have he : G.val = C := by
    change Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint (Spec.map φ ≫ x.left) hflat = C
    rw [Generated.EmbeddedBaseChange.generatedPullbackFamilyAtAffinePoint_baseChange,
      Flat.ClosedUniversality.flatClosedHilbertClassifier_pullback_eq hN hflat htest hr (𝟙 (Spec R)) F]
  exact ⟨C, he ▸ G.property⟩

theorem Flat.ClosedFamilies.FlatClosedHilbertFamily.coefficientBaseChange_val
    (F : Flat.ClosedFamilies.FlatClosedHilbertFamily R n P) (φ : R ⟶ A) :
    (F.coefficientBaseChange hN hflat htest hr φ).val =
      F.val.pullbackAlong (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n) (Spec.map φ) (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback φ n) := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

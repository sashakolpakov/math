import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.ClosedFamilyBaseChange

/-! # Classifier Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.ClassifierNaturality

noncomputable section

/-! Affine Hilbert classification is natural for actual coefficient pullbacks of embedded families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R A : CommRingCat.{u}} [IsNoetherianRing R] [IsNoetherianRing A]
variable {S : Scheme.{u}} {n B N : ℕ} {P : Polynomial ℚ}
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
variable (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (htest : Truncated.PolynomialTest.truncatedHilbertTestBound n N ≤ B)
variable (hr : Generated.RankTests.GeneratedHilbertRankTest n P N) (f : Spec R ⟶ S)

theorem flatClosedHilbertClassifier_coefficientBaseChange
    (F : Flat.ClosedFamilies.FlatClosedHilbertFamily R n P) (φ : R ⟶ A) :
    Flat.ClosedParameterEquivalence.flatClosedHilbertAffinePointEquiv hN hflat htest hr (Spec.map φ ≫ f)
      (F.coefficientBaseChange hN hflat htest hr φ) =
        (Over.homMk (Spec.map φ) rfl : Over.mk (Spec.map φ ≫ f) ⟶ Over.mk f) ≫
          Flat.ClosedParameterEquivalence.flatClosedHilbertAffinePointEquiv hN hflat htest hr f F := by
  let F' := F.coefficientBaseChange hN hflat htest hr φ
  apply (Flat.ClosedUniversality.flatClosedHilbertParameter_universal hN hflat htest hr (Spec.map φ ≫ f) F').unique
  · exact Flat.ClosedUniversality.flatClosedHilbertClassifier_pullback_eq hN hflat htest hr (Spec.map φ ≫ f) F'
  · change Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint
      (Spec.map φ ≫ (Flat.ClosedParameterEquivalence.flatClosedHilbertAffinePointEquiv hN hflat htest hr f F).left) hflat = F'.val
    rw [Generated.EmbeddedBaseChange.generatedPullbackFamilyAtAffinePoint_baseChange,
      Flat.ClosedUniversality.flatClosedHilbertClassifier_pullback_eq hN hflat htest hr f F]
    rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.ClassifierNaturality

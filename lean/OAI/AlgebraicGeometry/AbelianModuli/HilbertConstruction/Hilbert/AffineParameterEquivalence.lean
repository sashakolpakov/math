import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.SaturatedRoundTrip
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeneratedFamilyRecovery

/-! # Affine Parameter Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.AffineParameterEquivalence

noncomputable section

/-! The constructed open scheme classifies saturated flat Hilbert ideals on noetherian affine tests, under explicit uniform bounds and a finite numerical polynomial test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : CommRingCat.{u}} [IsNoetherianRing R] {S : Scheme.{u}} {n B N : ℕ} {P : Polynomial ℚ}
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
variable (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (htest : Truncated.PolynomialTest.truncatedHilbertTestBound n N ≤ B)
variable (hr : Generated.RankTests.GeneratedHilbertRankTest n P N) (f : Spec R ⟶ S)

def saturatedFlatHilbertAffinePointEquiv : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R n P ≃
    (Over.mk f ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N) :=
  (Generated.SaturatedRoundTrip.saturatedHilbertGeneratedDataEquiv hN hflat htest hr).trans (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f)

def saturatedFlatHilbertAffinePointFamilyIso (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R n P) :
    (Over.pullback (saturatedFlatHilbertAffinePointEquiv hN hflat htest hr f I).left).obj
      (Generated.FlatUniversalFamily.generatedFlatUniversalFamily S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N hflat).scheme ≅
        Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal :=
  Uniform.GeneratedFamilyRecovery.uniformGeneratedFlatParameterFamilyIso I.ideal I.saturated P I.hilbert N hN B hflat f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.AffineParameterEquivalence

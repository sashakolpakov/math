import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ClosedFamilies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.AffineParameterEquivalence

/-! # Closed Parameter Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ClosedParameterEquivalence

noncomputable section

/-! Actual flat closed Hilbert families over noetherian affine bases are classified by the constructed generated open parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : CommRingCat.{u}} [IsNoetherianRing R] {S : Scheme.{u}} {n B N : ℕ} {P : Polynomial ℚ}
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
variable (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (htest : Truncated.PolynomialTest.truncatedHilbertTestBound n N ≤ B)
variable (hr : Generated.RankTests.GeneratedHilbertRankTest n P N) (f : Spec R ⟶ S)

def flatClosedHilbertAffinePointEquiv : ClosedFamilies.FlatClosedHilbertFamily R n P ≃
    (Over.mk f ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N) :=
  ClosedFamilies.saturatedFlatHilbertClosedFamilyEquiv.symm.trans (Hilbert.AffineParameterEquivalence.saturatedFlatHilbertAffinePointEquiv hN hflat htest hr f)

def flatClosedHilbertAffinePointFamilyIso (F : ClosedFamilies.FlatClosedHilbertFamily R n P) :
    (Over.pullback (flatClosedHilbertAffinePointEquiv hN hflat htest hr f F).left).obj
      (Generated.FlatUniversalFamily.generatedFlatUniversalFamily S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N hflat).scheme ≅ F.val.scheme :=
  Hilbert.AffineParameterEquivalence.saturatedFlatHilbertAffinePointFamilyIso hN hflat htest hr f F.saturatedIdeal ≪≫ F.val.homogeneousFamilyIso

theorem flatClosedHilbertAffinePoint_injective : Function.Injective
    (flatClosedHilbertAffinePointEquiv hN hflat htest hr f) :=
  (flatClosedHilbertAffinePointEquiv hN hflat htest hr f).injective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ClosedParameterEquivalence

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ClosedUniversality

/-! # Families At Parameter Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.FamiliesAtParameterPoints

noncomputable section

/-! Every affine parameter point carries the actual pulled-back Hilbert family, and its classifier is the original point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : CommRingCat.{u}} [IsNoetherianRing R] {S : Scheme.{u}} {n B N : ℕ} {P : Polynomial ℚ}
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
variable (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (htest : Truncated.PolynomialTest.truncatedHilbertTestBound n N ≤ B)
variable (hr : Generated.RankTests.GeneratedHilbertRankTest n P N) (f : Spec R ⟶ S)
variable (x : Over.mk f ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N)

theorem hilbertParameter_pullback_eq_inverse :
    Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint x.left hflat =
      ((Flat.ClosedParameterEquivalence.flatClosedHilbertAffinePointEquiv hN hflat htest hr f).symm x).val := by
  let e := Flat.ClosedParameterEquivalence.flatClosedHilbertAffinePointEquiv hN hflat htest hr f
  have h := Flat.ClosedUniversality.flatClosedHilbertClassifier_pullback_eq hN hflat htest hr f (e.symm x)
  change Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint (e (e.symm x)).left hflat = _ at h
  rw [e.apply_symm_apply] at h
  exact h

def hilbertFamilyAtParameterPoint : Flat.ClosedFamilies.FlatClosedHilbertFamily R n P :=
  ⟨Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint x.left hflat, by
    rw [hilbertParameter_pullback_eq_inverse hN hflat htest hr f x]
    exact ((Flat.ClosedParameterEquivalence.flatClosedHilbertAffinePointEquiv hN hflat htest hr f).symm x).property⟩

theorem hilbertFamilyAtParameterPoint_classifier :
    Flat.ClosedParameterEquivalence.flatClosedHilbertAffinePointEquiv hN hflat htest hr f
      (hilbertFamilyAtParameterPoint hN hflat htest hr f x) = x := by
  have h : hilbertFamilyAtParameterPoint hN hflat htest hr f x =
      (Flat.ClosedParameterEquivalence.flatClosedHilbertAffinePointEquiv hN hflat htest hr f).symm x :=
    Subtype.ext (hilbertParameter_pullback_eq_inverse hN hflat htest hr f x)
  rw [h, Equiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.FamiliesAtParameterPoints

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ClosedParameterEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.PullbackAffineCharts

/-! # Closed Universality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ClosedUniversality

noncomputable section

/-! The actual embedded universal family has the unique affine classification property, including equality of defining ideal sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : CommRingCat.{u}} [IsNoetherianRing R] {S : Scheme.{u}} {n B N : ℕ} {P : Polynomial ℚ}
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
variable (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (htest : Truncated.PolynomialTest.truncatedHilbertTestBound n N ≤ B)
variable (hr : Generated.RankTests.GeneratedHilbertRankTest n P N) (f : Spec R ⟶ S)

theorem flatClosedHilbertClassifier_pullback_eq (F : ClosedFamilies.FlatClosedHilbertFamily R n P) :
    Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint
      (ClosedParameterEquivalence.flatClosedHilbertAffinePointEquiv hN hflat htest hr f F).left hflat = F.val := by
  let I := F.saturatedIdeal
  let D := I.generatedData N hN B
  apply Closed.Families.FlatClosedFamily.ext
  change ((Generated.PullbackAmbient.generatedPullbackFlatFamily S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N hflat).ideal).comap
    (Generated.PullbackAffineCharts.generatedPullbackAffineChart (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f D).left) = F.val.ideal
  rw [Generated.PullbackAffineCharts.generatedPullbackFlatFamily_affine_ideal, Generated.FamilyClassification.truncatedGeneratedClassifier_data f D]
  change ((Uniform.GeneratedCoordinates.uniformGeneratedData I.ideal I.saturated P I.hilbert N hN).truncate B).projectiveEmbedding.left.ker = F.val.ideal
  exact (Uniform.GeneratedReconstruction.uniformGeneratedTruncation_projectiveIdeal I.ideal I.saturated P I.hilbert N hN B
    ((Nat.le_add_right N _).trans hflat)).trans
      (HilbertScheme.Presentations.Projective.IdealEquivalence.GradedHilbert.projectiveQuotient_homogeneousIdealOfSheaf F.val.ideal)

include hN htest hr in
theorem flatClosedHilbertParameter_universal (F : ClosedFamilies.FlatClosedHilbertFamily R n P) :
    ∃! x : Over.mk f ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N,
      Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint x.left hflat = F.val := by
  let e := ClosedParameterEquivalence.flatClosedHilbertAffinePointEquiv hN hflat htest hr f
  refine ⟨e F, flatClosedHilbertClassifier_pullback_eq hN hflat htest hr f F, ?_⟩
  intro x hx
  have hfx := flatClosedHilbertClassifier_pullback_eq hN hflat htest hr f (e.symm x)
  change Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint (e (e.symm x)).left hflat = (e.symm x).val at hfx
  rw [e.apply_symm_apply] at hfx
  have he : e.symm x = F := Subtype.ext (hfx.symm.trans hx)
  exact (e.apply_symm_apply x).symm.trans (congrArg e he)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ClosedUniversality

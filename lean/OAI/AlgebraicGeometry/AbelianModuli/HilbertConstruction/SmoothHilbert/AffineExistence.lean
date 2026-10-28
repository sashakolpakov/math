import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.GeneratedData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ClosedUniversality

/-! # Affine Existence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.AffineExistence

noncomputable section

/-! Every smooth Hilbert family over an arbitrary affine ring is an actual pullback of the constructed finite parameter family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem smoothHilbertAffinePoint_exists
    {R : CommRingCat.{u}} {S : Scheme.{u}} {n B N : ℕ} {P : Polynomial ℚ}
    (F : Flat.ClosedFamilies.FlatClosedHilbertFamily R n P) [Smooth F.val.scheme.hom]
    (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (f : Spec R ⟶ S) :
    ∃ x : Over.mk f ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N,
      Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint x.left hflat = F.val := by
  obtain ⟨D, hD⟩ := F.exists_generatedData N hN B ((Nat.le_add_right N _).trans hflat)
  refine ⟨Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f D, ?_⟩
  apply Closed.Families.FlatClosedFamily.ext
  have h := Generated.PullbackAffineCharts.generatedPullbackFlatFamily_affine_ideal (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f D).left hflat
  rw [Generated.FamilyClassification.truncatedGeneratedClassifier_data f D] at h
  exact h.trans hD

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.AffineExistence

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedEmbeddingCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PrescribedFrameCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FramePointBaseChange

/-! # Pullback Coordinate Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert

noncomputable section

/-! The ordered coordinates of an actual normalized graph embedding
follow its original family under every change of base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding.markedPoint_baseChange
    (R : Type u) [CommRing R] {B T : Over (Spec (.of R))}
    {g N : ℕ} {δ : Fin g → ℕ} [NeZero N]
    {A : PolarizationData.PolarizedAbelianWithFullLevel g δ N B.left} {i : Fin (N ^ (2 * g))}
    (D : NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding R B A i) (f : T ⟶ B) (z : Fin (N ^ (2 * g))) :
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 T.left)) (A.pullback f.left).abelian
      (A.level.pullback f.left) (D.embedding.projectivePresentation.baseChange f.left)
      (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration z) =
        Balanced.FrameChartProjectivePoints.balancedFrameChartProjectivePoint R i D.chartIndex.frame D.chartIndex.additional
          D.chartIndex.coordinate D.chartIndex.exponent D.chartIndex.complement
          D.chartIndex.balanced D.chartIndex.complete T.left
          ((f ≫ D.chartPoint).left.appTop.hom.comp
            (Scheme.ΓSpecIso (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i
              D.chartIndex.exponent D.chartIndex.balanced))).inv.hom) z := by
  let j := D.chartIndex
  let ρ := D.chartPoint.left.appTop.hom.comp
    (Scheme.ΓSpecIso (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced))).inv.hom
  have hρ : (f ≫ D.chartPoint).left.appTop.hom.comp
      (Scheme.ΓSpecIso (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced))).inv.hom =
        f.left.appTop.hom.comp ρ := rfl
  exact (PrescribedFrameCoverage.StableHilbertCoverage.fullLevelMarkedPoint_pullback_eq B A.abelian A.level
    D.embedding.projectivePresentation f.left (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration z)).trans
      ((congrArg (fun p => Projective.SectionBaseChange.projectiveSectionBaseChange p f.left) (D.marked z)).trans
        ((Balanced.FramePointBaseChange.balancedFrameChartProjectivePoint_baseChange R i j.frame j.additional j.coordinate
          j.exponent j.complement j.balanced j.complete ρ f.left z).trans
            (congrArg (fun a => Balanced.FrameChartProjectivePoints.balancedFrameChartProjectivePoint R i j.frame j.additional j.coordinate
              j.exponent j.complement j.balanced j.complete T.left a z) hρ.symm)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert

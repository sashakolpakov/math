import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.BaseMapCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PullbackCoordinateCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.ArbitraryBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FramePointBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionEquations

/-! # Base Change Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.BaseChangeCoverage.StableHilbertCoverage

noncomputable section

/-! Normalized complete graph embeddings retain their actual ordered
configuration after affine base change and base-map equality. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (R : Type u) [CommRing R]

private theorem baseChangeEmbedding_comp_left
    {S T Z : Scheme.{u}} {X : Over S} {L : Line.Bundles.LineBundle X.left}
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom) (f : T ⟶ S)
    (M : Line.Bundles.LineBundle ((Over.pullback f).obj X).left)
    (eM : M.sheaf ≅ (L.pullback (CategoryTheory.Limits.pullback.fst X.hom f)).sheaf)
    (a : Z ⟶ ((Over.pullback f).obj X).left) :
    a ≫ (E.baseChangeWithLineIso f M eM).projectivePresentation.embedding.left =
      a ≫ (E.projectivePresentation.baseChange f).embedding.left :=
  congrArg (fun j => a ≫ j.left) (E.baseChangeWithLineIso_embedding f M eM)

private theorem normalizedPullback_marked
    {B T : Over (Spec (.of R))} {g N : ℕ} {δ : Fin g → ℕ} [NeZero N]
    {A : PolarizationData.PolarizedAbelianWithFullLevel g δ N B.left} {i : Fin (N ^ (2 * g))}
    (D : NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding R B A i) (f : T ⟶ B) (z : Fin (N ^ (2 * g))) :
    NormalizedEmbeddingCoverage.StableHilbertCoverage.indexedLevelSection (A.pullback f.left) z ≫
      (A.graphPowerEmbeddingBaseChange D.embedding f.left).projectivePresentation.embedding =
        Balanced.FrameChartProjectivePoints.balancedFrameChartProjectivePoint R i D.chartIndex.frame D.chartIndex.additional
          D.chartIndex.coordinate D.chartIndex.exponent D.chartIndex.complement
          D.chartIndex.balanced D.chartIndex.complete T.left
          ((f ≫ D.chartPoint).left.appTop.hom.comp
            (Scheme.ΓSpecIso (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i
              D.chartIndex.exponent D.chartIndex.balanced))).inv.hom) z := by
  apply Over.OverMorphism.ext
  exact (baseChangeEmbedding_comp_left (X := A.abelian.scheme) D.embedding f.left
    (A.pullback f.left).graphBundle (A.graphBundle_baseChangeIso f.left)
    (NormalizedEmbeddingCoverage.StableHilbertCoverage.indexedLevelSection (A.pullback f.left) z).left).trans
      (congrArg Over.Hom.left (D.markedPoint_baseChange R f z))

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding.pullback
    {B T : Over (Spec (.of R))} [IsAffine B.left] [IsNoetherianRing Γ(B.left, ⊤)] [IsAffine T.left]
    {g N : ℕ} {δ : Fin g → ℕ} [NeZero N]
    {A : PolarizationData.PolarizedAbelianWithFullLevel g δ N B.left} {i : Fin (N ^ (2 * g))}
    (D : NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding R B A i) (f : T ⟶ B)
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(B.left, ⊤))) :
    NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding R T (A.pullback f.left) i := by
  let E := A.graphPowerEmbeddingBaseChange D.embedding f.left
  refine {
    embedding := E
    degree_eq := D.degree_eq
    dimension_eq := D.dimension_eq
    complete := ⟨A.completeGraphPowerEmbeddingBaseChange D.embedding f.left hN hunit D.complete.some⟩
    chartIndex := D.chartIndex
    chartPoint := f ≫ D.chartPoint
    marked := normalizedPullback_marked R D f }

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.BaseChangeCoverage.StableHilbertCoverage

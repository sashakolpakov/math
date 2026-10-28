import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PresentationCompleteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrescribedLevelAmbientParameter

/-! # Prescribed Frame Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PrescribedFrameCoverage.StableHilbertCoverage

noncomputable section

/-! A prescribed projective frame remains the actual ordered marked
frame after pulling back its defining section equations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem pulledMarkedPoint_baseMap
    {S T : Scheme.{u}} (Z : Over S) {g N : ℕ}
    (A : Abelian.Schemes.AbelianScheme g Z.left) (level : A.FullLevel N)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (f : T ⟶ Z.left)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    (Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 T)) (A.pullback f) (level.pullback f)
      (P.baseChange f) c).left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap f P.dimension =
        f ≫ (Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint Z A level P c).left := by
  let x := A.fullLevelGlobalSection level c
  let y := (A.pullback f).fullLevelGlobalSection (level.pullback f) c
  have hy : y ≫ pullback.fst A.scheme.hom f = f ≫ x :=
    A.fullLevelGlobalSection_pullback level f c
  have hi : (P.baseChange f).embedding.left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap f P.dimension =
      pullback.fst A.scheme.hom f ≫ P.embedding.left :=
    Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding_baseMap P.embedding f
  exact (Category.assoc y _ _).trans ((congrArg (fun z => y ≫ z) hi).trans
    ((Category.assoc y _ _).symm.trans
      ((congrArg (fun z => z ≫ P.embedding.left) hy).trans (Category.assoc f x _))))

theorem fullLevelMarkedPoint_pullback_eq
    {S T : Scheme.{u}} (Z : Over S) {g N : ℕ}
    (A : Abelian.Schemes.AbelianScheme g Z.left) (level : A.FullLevel N)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (f : T ⟶ Z.left)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 T)) (A.pullback f) (level.pullback f)
      (P.baseChange f) c = Projective.SectionBaseChange.projectiveSectionBaseChange (Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint Z A level P c) f := by
  apply Projective.SectionBaseChange.projectiveSections_eq_of_baseMap f
  exact (pulledMarkedPoint_baseMap Z A level P f c).trans
    (Projective.SectionBaseChange.projectiveSectionBaseChange_baseMap (Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint Z A level P c) f).symm

theorem prescribedPullback_markedPoint
    {S T : Scheme.{u}} (Z : Over S)
    {g N m : ℕ} (A : Abelian.Schemes.AbelianScheme g Z.left) (level : A.FullLevel N)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (q : Fin m → (Over.mk (𝟙 Z.left) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver Z.left P.dimension))
    (c : T ⟶ Z.left) (hc : PrescribedLevelAmbientParameter.PrescribedFullLevelAmbientAt Z A level P labels q c) (z : Fin m) :
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 T)) (A.pullback c) (level.pullback c)
      (P.baseChange c) (labels z) = Projective.SectionBaseChange.projectiveSectionBaseChange (q z) c := by
  exact (fullLevelMarkedPoint_pullback_eq Z A level P c (labels z)).trans
    (Projective.SectionEquations.projectiveSections_baseChange_eq_of_pullback_eq c
      (Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint Z A level P (labels z)) (q z) (hc z))

theorem prescribedPullback_standardFrame
    {S T : Scheme.{u}} (Z : Over S)
    {g N m : ℕ} (A : Abelian.Schemes.AbelianScheme g Z.left) (level : A.FullLevel N)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (q : Fin m → (Over.mk (𝟙 Z.left) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver Z.left P.dimension))
    (c : T ⟶ Z.left) (hc : PrescribedLevelAmbientParameter.PrescribedFullLevelAmbientAt Z A level P labels q c)
    (σ : Fin (P.dimension + 1) → Fin m)
    (hq : ∀ k, q (σ k) = Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint Z.left P.dimension k) :
    ∀ k, Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 T)) (A.pullback c) (level.pullback c)
      (P.baseChange c) (labels (σ k)) = Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint T P.dimension k := by
  intro k
  exact (prescribedPullback_markedPoint Z A level P labels q c hc (σ k)).trans
    ((congrArg (fun a => Projective.SectionBaseChange.projectiveSectionBaseChange a c) (hq k)).trans
      (PresentationCompleteness.StableHilbertCoverage.standardBasisProjectivePoint_baseChange c P.dimension k))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PrescribedFrameCoverage.StableHilbertCoverage

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.ProjectiveRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ParameterMapNaturality

/-! # Point Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PointNaturality.HilbertLevelPullback

noncomputable section

/-! The original full-level universal family's recovery over an
arbitrary original Hilbert point, together with its pullback naturality. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem equalBaseEmbedding_left {S T : Scheme.{u}} {X : Over S} {n : ℕ}
    (j : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) {f g : T ⟶ S} (h : f = g) :
    (eqToIso (congrArg (fun a => (Over.pullback a).obj X) h)).hom.left ≫
      (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding j g).left = (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding j f).left :=
  congrArg Over.Hom.left (Projective.ParameterMapNaturality.ProjectivePullback.equalBase_embedding j h)

private theorem compositeIso_embedding_left {S W : Scheme.{u}} {X Y Z : Over S}
    (e : X ≅ Y) (q : Y ≅ Z) (i : Z.left ⟶ W) (j : Y.left ⟶ W) (k : X.left ⟶ W)
    (hq : q.hom.left ≫ i = j) (he : e.hom.left ≫ j = k) :
    (e ≪≫ q).hom.left ≫ i = k := by
  change (e.hom.left ≫ q.hom.left) ≫ i = k
  exact (Category.assoc _ _ _).trans ((congrArg (fun z => e.hom.left ≫ z) hq).trans he)

private theorem pulledEmbedding_mono {S T : Scheme.{u}} {X : Over S} {n : ℕ}
    (j : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (f : T ⟶ S) :
    Mono (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding j f).left := by
  let Q : Projective.ProjectivePresentations.ProjectivePresentation X := ⟨n, j, inferInstance⟩
  let : IsClosedImmersion (Q.baseChange f).embedding.left := (Q.baseChange f).closedImmersion
  exact inferInstanceAs (Mono (Q.baseChange f).embedding.left)

private theorem nativeComparison_natural
    {M N T U : Scheme.{u}} {X : Over M} {Y : Over N} {n : ℕ}
    (j : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver M n) (k : Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver N n)
    {x : T ⟶ M} {y : T ⟶ N} {x' : U ⟶ M} {y' : U ⟶ N}
    (cx : Over.mk x' ⟶ Over.mk x) (cy : Over.mk y' ⟶ Over.mk y)
    (hc : cx.left = cy.left)
    (e : (Over.pullback x).obj X ≅ (Over.pullback y).obj Y)
    (e' : (Over.pullback x').obj X ≅ (Over.pullback y').obj Y)
    (he : e.hom.left ≫ (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding k y).left =
      (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding j x).left)
    (he' : e'.hom.left ≫ (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding k y').left =
      (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding j x').left)
    [Mono (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding k y).left] :
    Single.ParameterBaseChange.singleParameterBaseChangeMap cx X ≫ e.hom.left =
      e'.hom.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap cy Y := by
  apply (cancel_mono (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding k y).left).mp
  calc
    _ = Single.ParameterBaseChange.singleParameterBaseChangeMap cx X ≫ (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding j x).left :=
      (Category.assoc _ _ _).trans (congrArg (fun a => Single.ParameterBaseChange.singleParameterBaseChangeMap cx X ≫ a) he)
    _ = (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding j x').left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap cx.left n :=
      Projective.ParameterMapNaturality.ProjectivePullback.parameterMap_embedding j cx
    _ = (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding j x').left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap cy.left n :=
      congrArg (fun q => (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding j x').left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap q n) hc
    _ = e'.hom.left ≫ ((Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding k y').left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap cy.left n) :=
      (congrArg (fun a => a ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap cy.left n) he'.symm).trans
        (Category.assoc _ _ _)
    _ = _ := (congrArg (fun a => e'.hom.left ≫ a)
      (Projective.ParameterMapNaturality.ProjectivePullback.parameterMap_embedding k cy).symm).trans (Category.assoc _ _ _).symm

variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ)
    (g : ℕ) (Pm Pi : Polynomial ℚ) (N : ℕ) [NeZero N]

/-- Recover the original Hilbert pullback at a specified Hilbert point. -/
def pointHilbertIso {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)
    (h : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n P)
    (hy : y ≫ PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N = h) :
    (((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n P g Pm Pi N)).pullback y.left).scheme ≅ (Over.pullback h.left).obj ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme) :=
  ProjectiveRecovery.HilbertLevelPullback.universalFamilyPullbackIso S n P g Pm Pi N y.left ≪≫
    eqToIso (congrArg (fun b => (Over.pullback b).obj ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme)) (congrArg Over.Hom.left hy))

theorem pointHilbertIso_embedding_left {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)
    (h : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n P)
    (hy : y ≫ PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N = h) :
    (pointHilbertIso S n P g Pm Pi N y h hy).hom.left ≫
      (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion) h.left).left =
        (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N)).embedding y.left).left := by
  let e := ProjectiveRecovery.HilbertLevelPullback.universalFamilyPullbackIso S n P g Pm Pi N y.left
  let q := eqToIso (congrArg (fun b => (Over.pullback b).obj ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme)) (congrArg Over.Hom.left hy))
  have hq := equalBaseEmbedding_left ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion) (congrArg Over.Hom.left hy)
  have he : e.hom.left ≫ (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion)
      (y ≫ PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N).left).left =
      (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N)).embedding y.left).left :=
    ProjectiveRecovery.HilbertLevelPullback.universalFamilyPullbackIso_embedding_left S n P g Pm Pi N y.left
  exact compositeIso_embedding_left e q _ _ _ hq he

theorem pointHilbertIso_embedding {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)
    (h : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n P)
    (hy : y ≫ PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N = h) :
    (pointHilbertIso S n P g Pm Pi N y h hy).hom ≫
      Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion h.left =
      Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).embedding y.left := by
  apply Over.OverMorphism.ext
  exact pointHilbertIso_embedding_left S n P g Pm Pi N y h hy

/-- Naturality allows different written composites for the same base
maps; the explicit equalities affect only the native pullback comparison. -/
theorem pointHilbertIso_natural {T U : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)
    (h : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n P)
    (hy : y ≫ PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N = h)
    (y' : U ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)
    (h' : U ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n P)
    (hy' : y' ≫ PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N = h')
    (u : U ⟶ T) (huy : u ≫ y = y') (huh : u ≫ h = h') :
    Single.ParameterBaseChange.singleParameterBaseChangeMap
      (Over.homMk u.left (congrArg Over.Hom.left huy) : Over.mk y'.left ⟶ Over.mk y.left)
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n P g Pm Pi N)).scheme ≫ (pointHilbertIso S n P g Pm Pi N y h hy).hom.left =
    (pointHilbertIso S n P g Pm Pi N y' h' hy').hom.left ≫
      Single.ParameterBaseChange.singleParameterBaseChangeMap
        (Over.homMk u.left (congrArg Over.Hom.left huh) : Over.mk h'.left ⟶ Over.mk h.left) ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme) := by
  have hmono : Mono (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion) h.left).left :=
    pulledEmbedding_mono (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion h.left
  exact @nativeComparison_natural _ _ _ _ _ _ _
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N)).embedding
    ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion) _ _ _ _ _ _ rfl
    (pointHilbertIso S n P g Pm Pi N y h hy)
    (pointHilbertIso S n P g Pm Pi N y' h' hy')
    (pointHilbertIso_embedding_left S n P g Pm Pi N y h hy)
    (pointHilbertIso_embedding_left S n P g Pm Pi N y' h' hy') hmono

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PointNaturality.HilbertLevelPullback

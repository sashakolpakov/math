import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ClassifierFactorization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InverseModelFactorization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.EmbeddedGraphFamilies

/-! # Parameter Point Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ParameterPointRecovery

noncomputable section

/-! Every point satisfying the exact graph-locus condition recovers a unique actual test-scheme morphism whose embedded graph is the pulled-back family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

local instance graphPointRecoveryPullbackFlat {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [Flat A.hom] :
    Flat ((Over.pullback f).obj A).hom := inferInstanceAs (Flat (Limits.pullback.snd A.hom f))

local instance graphPointRecoveryPullbackFinitePresentation {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S)
    [LocallyOfFinitePresentation A.hom] : LocallyOfFinitePresentation ((Over.pullback f).obj A).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (Limits.pullback.snd A.hom f))

local instance graphPointRecoveryPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [IsSeparated A.hom] :
    IsSeparated ((Over.pullback f).obj A).hom := inferInstanceAs (IsSeparated (Limits.pullback.snd A.hom f))

variable {S : Scheme.{u}} {T M : Over S} {A B : Over S} {n : ℕ}
variable (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver M.left n)) (c : T ⟶ M)
variable (h : (Over.pullback c.left).obj F.scheme ⟶ (Over.pullback c.left).obj (Product.ParameterBaseChange.parameterProductFamily A B M))

def graphParameterModelMap : (F.projectiveBaseChange c.left).scheme ⟶ Product.ParameterBaseChange.parameterProductFamily A B T :=
  InverseModelFactorization.modelFactorizationMap (F.projectiveBaseChangeIso c.left) (Product.ParameterBaseChange.productParameterBaseChangeIso c A B) h

theorem graphParameterModelMap_factors
    (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (hh : h ≫ (Over.pullback c.left).map (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding M.hom j) = (Over.pullback c.left).map F.inclusion) :
    graphParameterModelMap F c h ≫ RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j = (F.projectiveBaseChange c.left).inclusion :=
  InverseModelFactorization.modelFactorizationMap_factors (F.projectiveBaseChangeIso c.left) (Product.ParameterBaseChange.productParameterBaseChangeIso c A B)
    (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso (RelativeProjective.BaseMaps.relativeProjectiveBaseMap c.left n) c.left (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback c.left n))
    h ((Over.pullback c.left).map (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding M.hom j)) ((Over.pullback c.left).map F.inclusion)
    (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) (F.projectiveBaseChange c.left).inclusion
    (Product.ParameterIsoCompatibility.productParameterBaseChangeIso_embedding c j) (F.projectiveBaseChangeIso_inclusion c.left) hh

theorem graphParameterModelMap_projection_isIso
    [IsIso (h ≫ (Over.pullback c.left).map (fst ((Over.pullback M.hom).obj A) ((Over.pullback M.hom).obj B)))] :
    IsIso (graphParameterModelMap F c h ≫ fst ((Over.pullback T.hom).obj A) ((Over.pullback T.hom).obj B)) :=
  InverseModelFactorization.modelFactorizationMap_projection_isIso (F.projectiveBaseChangeIso c.left) (Product.ParameterBaseChange.productParameterBaseChangeIso c A B)
    (Single.ParameterBaseChange.singleParameterBaseChangeIso c A) h
    ((Over.pullback c.left).map (fst ((Over.pullback M.hom).obj A) ((Over.pullback M.hom).obj B)))
    (fst ((Over.pullback T.hom).obj A) ((Over.pullback T.hom).obj B)) (Product.ParameterIsoCompatibility.productParameterBaseChangeIso_fst c A B)

variable [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]

theorem graphParameter_factorization_iff_existsUnique
    (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] :
    FactorizationPointCondition.HasIsomorphicFactorization (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding M.hom j) F.inclusion
      (fst ((Over.pullback M.hom).obj A) ((Over.pullback M.hom).obj B)) c.left ↔
      ∃! p : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B,
        (MorphismGraphFamilies.morphismGraphFamily p).reembed (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) = F.projectiveBaseChange c.left := by
  constructor
  · rintro ⟨h, hh, hi⟩
    have : IsIso (h ≫ (Over.pullback c.left).map (fst ((Over.pullback M.hom).obj A) ((Over.pullback M.hom).obj B))) := hi
    let k := graphParameterModelMap F c h
    have : IsIso (k ≫ fst ((Over.pullback T.hom).obj A) ((Over.pullback T.hom).obj B)) :=
      graphParameterModelMap_projection_isIso F c h
    let p := ProjectedFamilyGraphRecovery.morphismOfProductProjection k
    have hp : (MorphismGraphFamilies.morphismGraphFamily p).reembed (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) = F.projectiveBaseChange c.left :=
      ProjectedFamilyGraphRecovery.projectedFamily_graph_recovery (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) (F.projectiveBaseChange c.left) k
        (graphParameterModelMap_factors F c h j hh)
    exact ⟨p, hp, fun q hq => Smooth.EmbeddedGraphFamilies.embeddedMorphismGraphFamily_injective (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) (hq.trans hp.symm)⟩
  · rintro ⟨p, hp, _⟩
    exact ClassifierFactorization.graphClassifier_hasIsomorphicFactorization F c j p hp.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ParameterPointRecovery

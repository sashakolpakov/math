import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.GraphFamilyRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.FamilyBaseChange

/-! # Graph Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.GraphRecovery

noncomputable section

/-! A recovered graph is exactly the pulled-back relative projective Hilbert family, in the test scheme's own projective space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

local instance relativeGraphPullbackFlat {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [Flat A.hom] :
    Flat ((Over.pullback f).obj A).hom := inferInstanceAs (Flat (Limits.pullback.snd A.hom f))

local instance relativeGraphPullbackFinitePresentation {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S)
    [LocallyOfFinitePresentation A.hom] : LocallyOfFinitePresentation ((Over.pullback f).obj A).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (Limits.pullback.snd A.hom f))

local instance relativeGraphPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [IsSeparated A.hom] :
    IsSeparated ((Over.pullback f).obj A).hom := inferInstanceAs (IsSeparated (Limits.pullback.snd A.hom f))

def relativeProjectiveGraphEmbedding {S T : Scheme.{u}} {A B : Over S} {n : ℕ}
    (f : T ⟶ S) (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) :
    (Over.pullback f).obj A ⊗ (Over.pullback f).obj B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T n :=
  Cartesian.PullbackGraphEmbedding.cartesianPullbackGraphEmbedding (BaseMaps.relativeProjectiveBaseMap f n) f
    (BaseMaps.relativeProjectiveBaseMap_isPullback f n) j

instance relativeProjectiveGraphEmbedding_closed {S T : Scheme.{u}} {A B : Over S} {n : ℕ}
    (f : T ⟶ S) (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] :
    IsClosedImmersion (relativeProjectiveGraphEmbedding f j).left :=
  Cartesian.PullbackGraphEmbedding.cartesianPullbackGraphEmbedding_closed (BaseMaps.relativeProjectiveBaseMap f n) f
    (BaseMaps.relativeProjectiveBaseMap_isPullback f n) j

theorem relativeProjectiveGraphFamily_recovery {S T : Scheme.{u}} {A B : Over S} {n : ℕ} {P : Polynomial ℚ}
    [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]
    (F : Families.RelativeProjectiveHilbertFamily S n P) (f : T ⟶ S)
    (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (h : (Over.pullback f).obj F.family.scheme ⟶ (Over.pullback f).obj (A ⊗ B))
    [IsIso (h ≫ (Over.pullback f).map (fst A B))]
    (hh : h ≫ (Over.pullback f).map j = (Over.pullback f).map F.family.inclusion) :
    (MorphismGraphFamilies.morphismGraphFamily (Pullback.ProjectedGraphRecovery.morphismOfPullbackProductProjection f h)).reembed (relativeProjectiveGraphEmbedding f j) =
      (F.pullback f).family :=
  Cartesian.GraphFamilyRecovery.cartesianGraphFamily_recovery F.family (BaseMaps.relativeProjectiveBaseMap f n) f
    (BaseMaps.relativeProjectiveBaseMap_isPullback f n) j h hh

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.GraphRecovery

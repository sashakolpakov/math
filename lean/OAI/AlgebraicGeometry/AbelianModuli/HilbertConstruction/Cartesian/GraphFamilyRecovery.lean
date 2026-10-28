import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.PullbackGraphEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.ReembeddingComposition

/-! # Graph Family Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.GraphFamilyRecovery

noncomputable section

/-! Graph recovery holds as equality of ideal-defined families in the chosen Cartesian ambient scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

local instance cartesianGraphPullbackFlat {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [Flat A.hom] :
    Flat ((Over.pullback f).obj A).hom := inferInstanceAs (Flat (Limits.pullback.snd A.hom f))

local instance cartesianGraphPullbackFinitePresentation {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S)
    [LocallyOfFinitePresentation A.hom] : LocallyOfFinitePresentation ((Over.pullback f).obj A).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (Limits.pullback.snd A.hom f))

local instance cartesianGraphPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [IsSeparated A.hom] :
    IsSeparated ((Over.pullback f).obj A).hom := inferInstanceAs (IsSeparated (Limits.pullback.snd A.hom f))

theorem cartesianGraphFamily_recovery
    {S T : Scheme.{u}} {A B P : Over S} {Q : Over T}
    [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]
    (F : Closed.Families.FlatClosedFamily P) (p : Q.left ⟶ P.left) (f : T ⟶ S) (hp : IsPullback p Q.hom P.hom f)
    (j : A ⊗ B ⟶ P) [IsClosedImmersion j.left]
    (h : (Over.pullback f).obj F.scheme ⟶ (Over.pullback f).obj (A ⊗ B))
    [IsIso (h ≫ (Over.pullback f).map (fst A B))]
    (hh : h ≫ (Over.pullback f).map j = (Over.pullback f).map F.inclusion) :
    (MorphismGraphFamilies.morphismGraphFamily (Pullback.ProjectedGraphRecovery.morphismOfPullbackProductProjection f h)).reembed
      (PullbackGraphEmbedding.cartesianPullbackGraphEmbedding p f hp j) = F.pullbackAlong p f hp := by
  have : Flat F.scheme.hom := F.flat
  have : LocallyOfFinitePresentation F.scheme.hom := F.locallyFinitePresentation
  have : IsClosedImmersion (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso p f hp).hom.left :=
    Grassmann.ProjectivePresentation.overIso_closedImmersion (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso p f hp)
  apply Closed.Families.FlatClosedFamily.reembed_injective (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso p f hp).hom
  dsimp only
  simp only [Closed.Families.FlatClosedFamily.reembed_comp, PullbackGraphEmbedding.cartesianPullbackGraphEmbedding_comp, F.pullbackAlong_reembedIso]
  exact (Pullback.ProjectedGraphRecovery.pullbackProjected_graph_recovery f F.inclusion j h hh).trans
    (F.baseChange_eq_ofEmbedding_pullbackInclusion f).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.GraphFamilyRecovery

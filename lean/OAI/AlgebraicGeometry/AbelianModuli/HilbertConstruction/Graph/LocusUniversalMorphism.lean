import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ProjectedGraphRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphicFactorizationRepresentation

/-! # Locus Universal Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.LocusUniversalMorphism

noncomputable section

/-! The constructed product-projection locus carries an actual universal morphism, whose graph recovers the pulled-back universal embedding family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

local instance graphLocusPullbackFlat {S T : Scheme.{u}} (c : T ⟶ S) (A : Over S) [Flat A.hom] :
    Flat ((Over.pullback c).obj A).hom := inferInstanceAs (Flat (Limits.pullback.snd A.hom c))

local instance graphLocusPullbackFinitePresentation {S T : Scheme.{u}} (c : T ⟶ S) (A : Over S)
    [LocallyOfFinitePresentation A.hom] : LocallyOfFinitePresentation ((Over.pullback c).obj A).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (Limits.pullback.snd A.hom c))

local instance graphLocusPullbackSeparated {S T : Scheme.{u}} (c : T ⟶ S) (A : Over S) [IsSeparated A.hom] :
    IsSeparated ((Over.pullback c).obj A).hom := inferInstanceAs (IsSeparated (Limits.pullback.snd A.hom c))

local instance graphLocusPullbackClosed {S T : Scheme.{u}} (c : T ⟶ S) {X P : Over S}
    (i : X ⟶ P) [IsClosedImmersion i.left] : IsClosedImmersion ((Over.pullback c).map i).left :=
  Projective.PresentationBaseChange.overPullback_map_closed i c

variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left] {X P A B : Over M.left}
variable [IsProper X.hom] [Flat X.hom] [IsProper A.hom]
variable (j : A ⊗ B ⟶ P) [IsClosedImmersion j.left] (i : X ⟶ P)

def graphLocusBaseMap : FactorizationIsomorphismParameter.factorizationIsomorphismParameter M j i (fst A B) ⟶ M :=
  FactorizationIsomorphismParameter.factorizationIsomorphismParameterInclusion M j i (fst A B) ≫ Proper.FactorizationParameter.properFactorizationParameterInclusion M j i

theorem graphLocusBaseMap_hasIsomorphicFactorization :
    FactorizationPointCondition.HasIsomorphicFactorization j i (fst A B) (graphLocusBaseMap M j i).left := by
  have h := (IsomorphicFactorizationPoints.isomorphicFactorizationPointEquiv M j i (fst A B)
    (FactorizationIsomorphismParameter.factorizationIsomorphismParameter M j i (fst A B)) (𝟙 _)).property
  simpa only [IsomorphicFactorizationPoints.isomorphicFactorizationPointEquiv_val, Category.id_comp, graphLocusBaseMap] using h

def graphLocusFactorization :
    (Over.pullback (graphLocusBaseMap M j i).left).obj X ⟶
      (Over.pullback (graphLocusBaseMap M j i).left).obj (A ⊗ B) :=
  (graphLocusBaseMap_hasIsomorphicFactorization M j i).choose

theorem graphLocusFactorization_fac :
    graphLocusFactorization M j i ≫ (Over.pullback (graphLocusBaseMap M j i).left).map j =
      (Over.pullback (graphLocusBaseMap M j i).left).map i :=
  (graphLocusBaseMap_hasIsomorphicFactorization M j i).choose_spec.1

instance graphLocusFactorization_projection_iso :
    IsIso (graphLocusFactorization M j i ≫ (Over.pullback (graphLocusBaseMap M j i).left).map (fst A B)) :=
  (graphLocusBaseMap_hasIsomorphicFactorization M j i).choose_spec.2

def graphLocusUniversalMorphism :
    (Over.pullback (graphLocusBaseMap M j i).left).obj A ⟶
      (Over.pullback (graphLocusBaseMap M j i).left).obj B :=
  Pullback.ProjectedGraphRecovery.morphismOfPullbackProductProjection (graphLocusBaseMap M j i).left (graphLocusFactorization M j i)

theorem graphLocusUniversalMorphism_graph
    [LocallyOfFinitePresentation X.hom] [IsClosedImmersion i.left]
    [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom] :
    (MorphismGraphFamilies.morphismGraphFamily (graphLocusUniversalMorphism M j i)).reembed
      (Pullback.ProjectedGraphRecovery.pullbackProductEmbedding (graphLocusBaseMap M j i).left j) =
        Closed.Families.FlatClosedFamily.ofEmbedding ((Over.pullback (graphLocusBaseMap M j i).left).map i) :=
  Pullback.ProjectedGraphRecovery.pullbackProjected_graph_recovery (graphLocusBaseMap M j i).left i j (graphLocusFactorization M j i)
    (graphLocusFactorization_fac M j i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.LocusUniversalMorphism

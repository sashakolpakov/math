import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectedEmbeddingGraphRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ProductProjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Projected Graph Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ProjectedGraphRecovery

noncomputable section

/-! A factorization with invertible first projection after arbitrary base change yields a morphism whose actual graph recovers the pulled-back embedding family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

local instance graphPullbackFlat {S T : Scheme.{u}} (c : T ⟶ S) (A : Over S) [Flat A.hom] :
    Flat ((Over.pullback c).obj A).hom := inferInstanceAs (Flat (Limits.pullback.snd A.hom c))

local instance graphPullbackFinitePresentation {S T : Scheme.{u}} (c : T ⟶ S) (A : Over S)
    [LocallyOfFinitePresentation A.hom] : LocallyOfFinitePresentation ((Over.pullback c).obj A).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (Limits.pullback.snd A.hom c))

local instance graphPullbackSeparated {S T : Scheme.{u}} (c : T ⟶ S) (A : Over S) [IsSeparated A.hom] :
    IsSeparated ((Over.pullback c).obj A).hom := inferInstanceAs (IsSeparated (Limits.pullback.snd A.hom c))

local instance graphPullbackClosed {S T : Scheme.{u}} (c : T ⟶ S) {X P : Over S}
    (i : X ⟶ P) [IsClosedImmersion i.left] : IsClosedImmersion ((Over.pullback c).map i).left :=
  Projective.PresentationBaseChange.overPullback_map_closed i c

def pullbackProductEmbedding {S T : Scheme.{u}} (c : T ⟶ S) {A B P : Over S} (j : A ⊗ B ⟶ P) :
    (Over.pullback c).obj A ⊗ (Over.pullback c).obj B ⟶ (Over.pullback c).obj P :=
  (Functor.Monoidal.μIso (Over.pullback c) A B).hom ≫ (Over.pullback c).map j

instance pullbackProductEmbedding_closed {S T : Scheme.{u}} (c : T ⟶ S) {A B P : Over S}
    (j : A ⊗ B ⟶ P) [IsClosedImmersion j.left] : IsClosedImmersion (pullbackProductEmbedding c j).left := by
  have : IsIso (Functor.Monoidal.μIso (Over.pullback c) A B).hom.left :=
    inferInstanceAs (IsIso ((Over.forget T).map (Functor.Monoidal.μIso (Over.pullback c) A B).hom))
  change IsClosedImmersion ((Functor.Monoidal.μIso (Over.pullback c) A B).hom.left ≫
    ((Over.pullback c).map j).left)
  infer_instance

def morphismOfPullbackProductProjection {S T : Scheme.{u}} (c : T ⟶ S) {X : Over T} {A B : Over S}
    (h : X ⟶ (Over.pullback c).obj (A ⊗ B)) [IsIso (h ≫ (Over.pullback c).map (fst A B))] :
    (Over.pullback c).obj A ⟶ (Over.pullback c).obj B := by
  letI : IsIso (ProductProjection.overPullbackProductMap c A B h ≫ fst ((Over.pullback c).obj A) ((Over.pullback c).obj B)) := by
    rw [ProductProjection.overPullbackProductMap_fst]
    infer_instance
  exact ProjectedFamilyGraphRecovery.morphismOfProductProjection (ProductProjection.overPullbackProductMap c A B h)

theorem pullbackProjected_graph_recovery
    {S T : Scheme.{u}} (c : T ⟶ S) {X A B P : Over S}
    [Flat X.hom] [LocallyOfFinitePresentation X.hom]
    [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]
    (i : X ⟶ P) [IsClosedImmersion i.left] (j : A ⊗ B ⟶ P) [IsClosedImmersion j.left]
    (h : (Over.pullback c).obj X ⟶ (Over.pullback c).obj (A ⊗ B))
    [IsIso (h ≫ (Over.pullback c).map (fst A B))]
    (hh : h ≫ (Over.pullback c).map j = (Over.pullback c).map i) :
    (MorphismGraphFamilies.morphismGraphFamily (morphismOfPullbackProductProjection c h)).reembed (pullbackProductEmbedding c j) =
      Closed.Families.FlatClosedFamily.ofEmbedding ((Over.pullback c).map i) := by
  let k := ProductProjection.overPullbackProductMap c A B h
  have : IsIso (k ≫ fst ((Over.pullback c).obj A) ((Over.pullback c).obj B)) := by
    change IsIso (ProductProjection.overPullbackProductMap c A B h ≫ _)
    rw [ProductProjection.overPullbackProductMap_fst]
    infer_instance
  change (MorphismGraphFamilies.morphismGraphFamily (ProjectedFamilyGraphRecovery.morphismOfProductProjection k)).reembed (pullbackProductEmbedding c j) = _
  apply ProjectedEmbeddingGraphRecovery.projectedEmbedding_graph_recovery ((Over.pullback c).map i) (pullbackProductEmbedding c j) k
  dsimp only [k, ProductProjection.overPullbackProductMap, pullbackProductEmbedding]
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact hh

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ProjectedGraphRecovery

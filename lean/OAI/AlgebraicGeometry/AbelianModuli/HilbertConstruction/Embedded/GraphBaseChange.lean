import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GraphEmbeddingCartesian
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyKernelRecovery

/-! # Graph Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.GraphBaseChange

noncomputable section

/-! Actual projectively embedded morphism graphs commute with arbitrary base change through the specified relative projective embedding. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

local instance embeddedGraphPullbackFlat {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [Flat A.hom] :
    Flat ((Over.pullback f).obj A).hom := inferInstanceAs (Flat (pullback.snd A.hom f))

local instance embeddedGraphPullbackFinitePresentation {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S)
    [LocallyOfFinitePresentation A.hom] : LocallyOfFinitePresentation ((Over.pullback f).obj A).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.snd A.hom f))

local instance embeddedGraphPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [IsSeparated A.hom] :
    IsSeparated ((Over.pullback f).obj A).hom := inferInstanceAs (IsSeparated (pullback.snd A.hom f))

local instance embeddedGraphCompositeClosed {S : Scheme.{u}} {X Y Z : Over S}
    (i : X ⟶ Y) [IsClosedImmersion i.left] (j : Y ⟶ Z) [IsClosedImmersion j.left] :
    IsClosedImmersion (i ≫ j).left := inferInstanceAs (IsClosedImmersion (i.left ≫ j.left))

theorem embeddedGraph_baseChange_isPullback {S T : Scheme.{u}} {A B : Over S} {n : ℕ}
    (f : T ⟶ S) (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (p : A ⟶ B) :
    IsPullback (MorphismGraphFamilies.familyGraph ((Over.pullback f).map p) ≫ RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f j).left
      (pullback.fst A.hom f) (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n) (MorphismGraphFamilies.familyGraph p ≫ j).left :=
  (Graph.FamilyNaturality.familyGraph_baseChange_isPullback f p).paste_horiz (Relative.GraphEmbeddingCartesian.relativeProjectiveGraphEmbedding_isPullback f j)

theorem embeddedMorphismGraphFamily_projectiveBaseChange
    {S T : Scheme.{u}} {A B : Over S} {n : ℕ}
    [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]
    (f : T ⟶ S) (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (p : A ⟶ B) :
    ((MorphismGraphFamilies.morphismGraphFamily p).reembed j).projectiveBaseChange f =
      (MorphismGraphFamilies.morphismGraphFamily ((Over.pullback f).map p)).reembed (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f j) := by
  change ((Closed.Families.FlatClosedFamily.ofEmbedding (MorphismGraphFamilies.familyGraph p)).reembed j).projectiveBaseChange f =
    (Closed.Families.FlatClosedFamily.ofEmbedding (MorphismGraphFamilies.familyGraph ((Over.pullback f).map p))).reembed (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f j)
  rw [Closed.Families.FlatClosedFamily.ofEmbedding_reembed, Closed.Families.FlatClosedFamily.ofEmbedding_reembed]
  apply Closed.Families.FlatClosedFamily.ext
  change (MorphismGraphFamilies.familyGraph p ≫ j).left.ker.comap (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n) =
    (MorphismGraphFamilies.familyGraph ((Over.pullback f).map p) ≫ RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f j).left.ker
  exact (Graph.FamilyBaseChange.closedImmersion_ker_baseChange (embeddedGraph_baseChange_isPullback f j p)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.GraphBaseChange

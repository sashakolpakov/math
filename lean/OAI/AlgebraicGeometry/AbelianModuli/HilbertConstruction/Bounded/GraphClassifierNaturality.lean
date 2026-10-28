import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.EmbeddedMorphismFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GraphParameterPointEquivalence

/-! # Graph Classifier Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.GraphClassifierNaturality

noncomputable section

/-! The actual graph-parameter classifier commutes with geometric base change of morphisms on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

local instance boundedClassifierPullbackSmooth {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [Smooth A.hom] :
    Smooth ((Over.pullback f).obj A).hom := inferInstanceAs (Smooth (Limits.pullback.snd A.hom f))

local instance boundedClassifierPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [IsSeparated A.hom] :
    IsSeparated ((Over.pullback f).obj A).hom := inferInstanceAs (IsSeparated (Limits.pullback.snd A.hom f))

theorem smoothEmbeddedGraphParameterClassifier_natural
    {S : Scheme.{u}} [IsNoetherian S] {A B : Over S} {n : ℕ}
    [IsProper A.hom] [Smooth A.hom] [IsSeparated B.hom]
    (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)
    {U T : Over S} (f : U ⟶ T) (p : (EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor j P).obj (.op T)) :
    HilbertConstruction.Smooth.GraphClassifierLift.smoothEmbeddedGraphParameterClassifier j P ((EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor j P).map f.op p) =
      f ≫ HilbertConstruction.Smooth.GraphClassifierLift.smoothEmbeddedGraphParameterClassifier j P p := by
  let q := (EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor j P).map f.op p
  apply (HilbertConstruction.Smooth.GraphParameterUniversality.smoothEmbeddedGraphParameterClassifier_family_existsUnique j P q).unique
  · exact HilbertConstruction.Smooth.GraphParameterUniversality.smoothEmbeddedGraphParameterClassifier_classifies j P q
  · calc
      (HilbertConstruction.Smooth.GraphParameterUniversality.smoothEmbeddedGraphUniversalFamily j P).pullback (f ≫ HilbertConstruction.Smooth.GraphClassifierLift.smoothEmbeddedGraphParameterClassifier j P p).left =
          ((HilbertConstruction.Smooth.GraphParameterUniversality.smoothEmbeddedGraphUniversalFamily j P).pullback (HilbertConstruction.Smooth.GraphClassifierLift.smoothEmbeddedGraphParameterClassifier j P p).left).pullback f.left :=
        ((HilbertConstruction.Smooth.GraphParameterUniversality.smoothEmbeddedGraphUniversalFamily j P).pullback_comp (HilbertConstruction.Smooth.GraphClassifierLift.smoothEmbeddedGraphParameterClassifier j P p).left f.left).symm
      _ = (Embedded.GraphHilbertBaseChange.embeddedGraphHilbertFamily (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p).pullback f.left :=
        congrArg (fun F => F.pullback f.left) (HilbertConstruction.Smooth.GraphParameterUniversality.smoothEmbeddedGraphParameterClassifier_classifies j P p)
      _ = Embedded.GraphHilbertBaseChange.embeddedGraphHilbertFamily (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding U.hom j) P q := by
        apply RelativeProjective.Families.RelativeProjectiveHilbertFamily.ext
        exact Geometric.EmbeddedGraphNaturality.geometricEmbeddedGraph_baseChange f j p.val

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.GraphClassifierNaturality

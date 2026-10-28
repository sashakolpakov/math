import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GraphEmbeddingComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.FamilyConjugation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.GraphHilbertBaseChange

/-! # Embedded Graph Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The graph in the fixed product embedding commutes with actual geometric family-morphism pullback, preserving its prescribed Hilbert polynomial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

local instance Geometric.EmbeddedGraphNaturality.geometricGraphPullbackFlat {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [Flat A.hom] :
    Flat ((Over.pullback f).obj A).hom := inferInstanceAs (Flat (Limits.pullback.snd A.hom f))

local instance Geometric.EmbeddedGraphNaturality.geometricGraphPullbackFinitePresentation {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S)
    [LocallyOfFinitePresentation A.hom] : LocallyOfFinitePresentation ((Over.pullback f).obj A).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (Limits.pullback.snd A.hom f))

local instance Geometric.EmbeddedGraphNaturality.geometricGraphPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [IsSeparated A.hom] :
    IsSeparated ((Over.pullback f).obj A).hom := inferInstanceAs (IsSeparated (Limits.pullback.snd A.hom f))

variable {S : Scheme.{u}} {U T : Over S} {A B : Over S} {n : ℕ}
variable [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]
variable (f : U ⟶ T) (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable (p : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B)

theorem Geometric.EmbeddedGraphNaturality.geometricEmbeddedGraph_baseChange :
    ((MorphismGraphFamilies.morphismGraphFamily p).reembed (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j)).projectiveBaseChange f.left =
      (MorphismGraphFamilies.morphismGraphFamily (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange f p)).reembed (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding U.hom j) := by
  have h := Graph.FamilyConjugation.morphismGraphFamily_conjugation_reembedding (Single.ParameterBaseChange.singleParameterBaseChangeIso f A) (Single.ParameterBaseChange.singleParameterBaseChangeIso f B)
    ((Over.pullback f.left).map p) (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f.left (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j))
  simp only [Relative.GraphEmbeddingComposition.relativeProjectiveGraphEmbedding_parameter_composition] at h
  exact (Embedded.GraphBaseChange.embeddedMorphismGraphFamily_projectiveBaseChange f.left (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) p).trans h.symm

theorem Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial.geometricBaseChange (P : Polynomial ℚ)
    (hp : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding U.hom j) P (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange f p) := by
  let F := Embedded.GraphHilbertBaseChange.embeddedGraphHilbertFamily (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P ⟨p, hp⟩
  have he : (F.pullback f.left).family =
      (MorphismGraphFamilies.morphismGraphFamily (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange f p)).reembed (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding U.hom j) :=
    Geometric.EmbeddedGraphNaturality.geometricEmbeddedGraph_baseChange f j p
  intro K _ x
  have h := (F.pullback f.left).fieldHilbert K x
  rwa [he] at h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

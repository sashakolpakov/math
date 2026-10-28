import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.EmbeddedGraphNaturality

/-! # Embedded Morphism Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.EmbeddedMorphismFunctor

noncomputable section

/-! Morphisms with the prescribed embedded graph polynomial form a subfunctor of the actual geometric family-morphism functor on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

local instance boundedMorphismPullbackFlat {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [Flat A.hom] :
    Flat ((Over.pullback f).obj A).hom := inferInstanceAs (Flat (Limits.pullback.snd A.hom f))

local instance boundedMorphismPullbackFinitePresentation {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S)
    [LocallyOfFinitePresentation A.hom] : LocallyOfFinitePresentation ((Over.pullback f).obj A).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (Limits.pullback.snd A.hom f))

local instance boundedMorphismPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [IsSeparated A.hom] :
    IsSeparated ((Over.pullback f).obj A).hom := inferInstanceAs (IsSeparated (Limits.pullback.snd A.hom f))

variable {S : Scheme.{u}} {A B : Over S} {n : ℕ}
variable [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]
variable (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)

def boundedEmbeddedMorphismSubfunctor : Subfunctor (Geometric.MorphismFunctor.geometricFamilyMorphismFunctor A B) where
  obj T := {p | Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.unop.hom j) P p}
  map f p hp := Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial.geometricBaseChange f.unop j p P hp

def boundedEmbeddedMorphismFunctor : (Over S)ᵒᵖ ⥤ Type u := (boundedEmbeddedMorphismSubfunctor j P).toFunctor

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.EmbeddedMorphismFunctor

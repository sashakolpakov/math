import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.GraphBaseChange

/-! # Graph Hilbert Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.GraphHilbertBaseChange

noncomputable section

/-! The prescribed field-fiber Hilbert polynomial of an embedded morphism graph is preserved by every base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

local instance embeddedHilbertPullbackFlat {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [Flat A.hom] :
    Flat ((Over.pullback f).obj A).hom := inferInstanceAs (Flat (Limits.pullback.snd A.hom f))

local instance embeddedHilbertPullbackFinitePresentation {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S)
    [LocallyOfFinitePresentation A.hom] : LocallyOfFinitePresentation ((Over.pullback f).obj A).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (Limits.pullback.snd A.hom f))

local instance embeddedHilbertPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [IsSeparated A.hom] :
    IsSeparated ((Over.pullback f).obj A).hom := inferInstanceAs (IsSeparated (Limits.pullback.snd A.hom f))

variable {S : Scheme.{u}} {A B : Over S} {n : ℕ}
variable [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]
variable (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)

def HasEmbeddedGraphHilbertPolynomial (p : A ⟶ B) : Prop :=
  ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ S),
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (((MorphismGraphFamilies.morphismGraphFamily p).reembed j).affineProjectivePullback x).homogeneousIdeal.toIdeal P

def embeddedGraphHilbertFamily (p : {p : A ⟶ B // HasEmbeddedGraphHilbertPolynomial j P p}) :
    RelativeProjective.Families.RelativeProjectiveHilbertFamily S n P where
  family := (MorphismGraphFamilies.morphismGraphFamily p.val).reembed j
  fieldHilbert := p.property

theorem HasEmbeddedGraphHilbertPolynomial.baseChange {T : Scheme.{u}} {p : A ⟶ B}
    (hp : HasEmbeddedGraphHilbertPolynomial j P p) (f : T ⟶ S) :
    HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f j) P ((Over.pullback f).map p) := by
  let F := embeddedGraphHilbertFamily j P ⟨p, hp⟩
  have he : (F.pullback f).family =
      (MorphismGraphFamilies.morphismGraphFamily ((Over.pullback f).map p)).reembed (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f j) :=
    GraphBaseChange.embeddedMorphismGraphFamily_projectiveBaseChange f j p
  intro K _ x
  have h := (F.pullback f).fieldHilbert K x
  rwa [he] at h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.GraphHilbertBaseChange

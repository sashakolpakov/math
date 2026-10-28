import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.EmbeddedGraphFamilies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.UniversalProperty

/-! # Embedded Graph Classification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.EmbeddedGraphClassification

noncomputable section

/-! Smooth morphism graphs with a prescribed Hilbert polynomial have faithful, unique classifiers in the actual smooth Hilbert parameter over arbitrary test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} {T : Over S} {A B : Over T.left} {n : ℕ}
variable [Smooth A.hom] [IsSeparated B.hom]
variable (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T.left n) [IsClosedImmersion j.left] (P : Polynomial ℚ)

theorem smoothEmbeddedGraphClassifier_existsUnique
    (p : {p : A ⟶ B // Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P p}) :
    ∃! c : T ⟶ SmoothHilbert.Parameter.smoothHilbertParameter S n P,
      (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).pullback c.left = Embedded.GraphHilbertBaseChange.embeddedGraphHilbertFamily j P p :=
  SmoothHilbert.UniversalProperty.smoothHilbertUniversalFamily_existsUnique
    ⟨Embedded.GraphHilbertBaseChange.embeddedGraphHilbertFamily j P p, EmbeddedGraphFamilies.embeddedGraphHilbertFamily_smooth j P p⟩

def smoothEmbeddedGraphClassifier
    (p : {p : A ⟶ B // Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P p}) : T ⟶ SmoothHilbert.Parameter.smoothHilbertParameter S n P :=
  (smoothEmbeddedGraphClassifier_existsUnique j P p).choose

theorem smoothEmbeddedGraphClassifier_classifies
    (p : {p : A ⟶ B // Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P p}) :
    (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).pullback (smoothEmbeddedGraphClassifier j P p).left =
      Embedded.GraphHilbertBaseChange.embeddedGraphHilbertFamily j P p :=
  (smoothEmbeddedGraphClassifier_existsUnique j P p).choose_spec.1

theorem smoothEmbeddedGraphClassifier_injective :
    Function.Injective (fun p => smoothEmbeddedGraphClassifier j P p) := by
  intro p q h
  apply Subtype.ext
  apply EmbeddedGraphFamilies.embeddedMorphismGraphFamily_injective j
  have he := (smoothEmbeddedGraphClassifier_classifies j P p).symm.trans
    ((congrArg (fun c : T ⟶ SmoothHilbert.Parameter.smoothHilbertParameter S n P =>
      (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).pullback c.left) h).trans
        (smoothEmbeddedGraphClassifier_classifies j P q))
  exact congrArg RelativeProjective.Families.RelativeProjectiveHilbertFamily.family he

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.EmbeddedGraphClassification

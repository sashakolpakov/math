import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GraphClassifierLift

/-! # Graph Parameter Universality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GraphParameterUniversality

noncomputable section

/-! The fixed-embedding graph parameter carries a smooth Hilbert family that uniquely classifies every prescribed smooth-source morphism graph. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

local instance graphUniversalityPullbackSmooth {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [Smooth A.hom] :
    Smooth ((Over.pullback f).obj A).hom := inferInstanceAs (Smooth (Limits.pullback.snd A.hom f))

local instance graphUniversalityPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [IsSeparated A.hom] :
    IsSeparated ((Over.pullback f).obj A).hom := inferInstanceAs (IsSeparated (Limits.pullback.snd A.hom f))

variable {S : Scheme.{u}} [IsNoetherian S] {A B : Over S} {n : ℕ} [IsProper A.hom]
variable (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)

def smoothEmbeddedGraphUniversalFamily :
    RelativeProjective.Families.RelativeProjectiveHilbertFamily (EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P).left n P :=
  (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).pullback (EmbeddedGraphParameters.smoothEmbeddedGraphParameterHilbertMap j P).left

theorem smoothEmbeddedGraphUniversalFamily_smooth :
    Smooth (smoothEmbeddedGraphUniversalFamily j P).family.scheme.hom := by
  have : Smooth (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).family.scheme.hom := SmoothHilbert.Parameter.smoothHilbertUniversalFamily_smooth S n P
  exact (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).pullback_smooth (EmbeddedGraphParameters.smoothEmbeddedGraphParameterHilbertMap j P).left

variable {T : Over S} [Smooth A.hom] [IsSeparated B.hom]
variable (p : {p : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B //
  Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p})

theorem smoothEmbeddedGraphParameterClassifier_classifies :
    (smoothEmbeddedGraphUniversalFamily j P).pullback (GraphClassifierLift.smoothEmbeddedGraphParameterClassifier j P p).left =
      Embedded.GraphHilbertBaseChange.embeddedGraphHilbertFamily (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p := by
  change ((SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).pullback (EmbeddedGraphParameters.smoothEmbeddedGraphParameterHilbertMap j P).left).pullback _ = _
  rw [RelativeProjective.Families.RelativeProjectiveHilbertFamily.pullback_comp]
  have hc := congrArg Over.Hom.left (GraphClassifierLift.smoothEmbeddedGraphParameterClassifier_hilbert j P p)
  change (GraphClassifierLift.smoothEmbeddedGraphParameterClassifier j P p).left ≫ (EmbeddedGraphParameters.smoothEmbeddedGraphParameterHilbertMap j P).left =
    (EmbeddedGraphClassification.smoothEmbeddedGraphClassifier (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p).left at hc
  rw [hc]
  exact EmbeddedGraphClassification.smoothEmbeddedGraphClassifier_classifies (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p

theorem smoothEmbeddedGraphParameterClassifier_family_existsUnique :
    ∃! y : T ⟶ EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P,
      (smoothEmbeddedGraphUniversalFamily j P).pullback y.left =
        Embedded.GraphHilbertBaseChange.embeddedGraphHilbertFamily (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p := by
  refine ⟨GraphClassifierLift.smoothEmbeddedGraphParameterClassifier j P p, smoothEmbeddedGraphParameterClassifier_classifies j P p, ?_⟩
  intro y hy
  apply (cancel_mono (EmbeddedGraphParameters.smoothEmbeddedGraphParameterHilbertMap j P)).mp
  apply (EmbeddedGraphClassification.smoothEmbeddedGraphClassifier_existsUnique (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p).unique
  · change (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).pullback (y.left ≫ (EmbeddedGraphParameters.smoothEmbeddedGraphParameterHilbertMap j P).left) = _
    exact ((SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).pullback_comp (EmbeddedGraphParameters.smoothEmbeddedGraphParameterHilbertMap j P).left y.left).symm.trans hy
  · have h := smoothEmbeddedGraphParameterClassifier_classifies j P p
    exact ((SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).pullback_comp (EmbeddedGraphParameters.smoothEmbeddedGraphParameterHilbertMap j P).left
      (GraphClassifierLift.smoothEmbeddedGraphParameterClassifier j P p).left).symm.trans h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GraphParameterUniversality

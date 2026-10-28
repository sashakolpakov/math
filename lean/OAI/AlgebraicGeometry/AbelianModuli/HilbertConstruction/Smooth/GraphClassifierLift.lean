import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ClassifierFactorization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ParameterPointProjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.EmbeddedGraphClassification

/-! # Graph Classifier Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GraphClassifierLift

noncomputable section

/-! Every smooth-source morphism with the prescribed embedded graph polynomial has a unique point of the constructed graph parameter over its actual Hilbert classifier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

local instance graphClassifierLiftPullbackSmooth {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [Smooth A.hom] :
    Smooth ((Over.pullback f).obj A).hom := inferInstanceAs (Smooth (Limits.pullback.snd A.hom f))

local instance graphClassifierLiftPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [IsSeparated A.hom] :
    IsSeparated ((Over.pullback f).obj A).hom := inferInstanceAs (IsSeparated (Limits.pullback.snd A.hom f))

variable {S : Scheme.{u}} [IsNoetherian S] {T : Over S} {A B : Over S} {n : ℕ}
variable [IsProper A.hom] [Smooth A.hom] [IsSeparated B.hom]
variable (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)
variable (p : {p : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B //
  Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p})

omit [AlgebraicGeometry.IsNoetherian S] [IsProper A.hom] in
theorem smoothGraphHilbertClassifier_factorization :
    FactorizationPointCondition.HasIsomorphicFactorization (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding (SmoothHilbert.Parameter.smoothHilbertParameter S n P).hom j)
      (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).family.inclusion
      (fst ((Over.pullback (SmoothHilbert.Parameter.smoothHilbertParameter S n P).hom).obj A)
        ((Over.pullback (SmoothHilbert.Parameter.smoothHilbertParameter S n P).hom).obj B))
      (EmbeddedGraphClassification.smoothEmbeddedGraphClassifier (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p).left :=
  Graph.ClassifierFactorization.graphClassifier_hasIsomorphicFactorization (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).family
    (EmbeddedGraphClassification.smoothEmbeddedGraphClassifier (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p) j p.val
    (congrArg RelativeProjective.Families.RelativeProjectiveHilbertFamily.family
      (EmbeddedGraphClassification.smoothEmbeddedGraphClassifier_classifies (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p))

def smoothEmbeddedGraphParameterClassifier : T ⟶ EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P :=
  (EmbeddedGraphParameters.smoothEmbeddedGraphParameterPointEquiv j P T).symm
    ⟨EmbeddedGraphClassification.smoothEmbeddedGraphClassifier (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p,
      smoothGraphHilbertClassifier_factorization j P p⟩

theorem smoothEmbeddedGraphParameterClassifier_hilbert :
    smoothEmbeddedGraphParameterClassifier j P p ≫ EmbeddedGraphParameters.smoothEmbeddedGraphParameterHilbertMap j P =
      EmbeddedGraphClassification.smoothEmbeddedGraphClassifier (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p := by
  have h := congrArg Subtype.val ((EmbeddedGraphParameters.smoothEmbeddedGraphParameterPointEquiv j P T).apply_symm_apply
    ⟨EmbeddedGraphClassification.smoothEmbeddedGraphClassifier (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p,
      smoothGraphHilbertClassifier_factorization j P p⟩)
  change (EmbeddedGraphParameters.smoothEmbeddedGraphParameterPointEquiv j P T (smoothEmbeddedGraphParameterClassifier j P p)).val = _ at h
  rwa [Graph.ParameterPointProjection.smoothEmbeddedGraphParameterPointEquiv_val] at h

theorem smoothEmbeddedGraphParameterClassifier_existsUnique :
    ∃! y : T ⟶ EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P,
      y ≫ EmbeddedGraphParameters.smoothEmbeddedGraphParameterHilbertMap j P =
        EmbeddedGraphClassification.smoothEmbeddedGraphClassifier (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p :=
  ⟨smoothEmbeddedGraphParameterClassifier j P p, smoothEmbeddedGraphParameterClassifier_hilbert j P p,
    fun _ hy => (cancel_mono _).mp (hy.trans (smoothEmbeddedGraphParameterClassifier_hilbert j P p).symm)⟩

theorem smoothEmbeddedGraphParameterClassifier_injective :
    Function.Injective (fun p => smoothEmbeddedGraphParameterClassifier (T := T) j P p) := by
  intro p q h
  apply EmbeddedGraphClassification.smoothEmbeddedGraphClassifier_injective (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P
  exact (smoothEmbeddedGraphParameterClassifier_hilbert j P p).symm.trans
    ((congrArg (fun y : T ⟶ EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P => y ≫ EmbeddedGraphParameters.smoothEmbeddedGraphParameterHilbertMap j P) h).trans
      (smoothEmbeddedGraphParameterClassifier_hilbert j P q))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GraphClassifierLift

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.HilbertParameterGeometry
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.LocusUniversalMorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.GraphRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.BaseMapPullback

/-! # Embedded Graph Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.EmbeddedGraphParameters

noncomputable section

/-! A fixed closed product embedding defines a quasi-projective smooth graph parameter by its exact relative projective base changes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

local instance embeddedGraphParameterPullbackProper {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [IsProper A.hom] :
    IsProper ((Over.pullback f).obj A).hom := inferInstanceAs (IsProper (Limits.pullback.snd A.hom f))

variable {S : Scheme.{u}} [IsNoetherian S] {A B : Over S} {n : ℕ} [IsProper A.hom]
variable (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)

def smoothEmbeddedGraphParameter : Over S :=
  FactorizationIsomorphismParameter.factorizationIsomorphismParameter (SmoothHilbert.Parameter.smoothHilbertParameter S n P)
    (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding (SmoothHilbert.Parameter.smoothHilbertParameter S n P).hom j)
    (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).family.inclusion (fst _ _)

def smoothEmbeddedGraphParameterQuasiProjectivePresentation :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (smoothEmbeddedGraphParameter j P) :=
  FactorizationIsomorphismParameter.factorizationIsomorphismParameterQuasiProjectivePresentation (SmoothHilbert.Parameter.smoothHilbertParameter S n P)
    (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding (SmoothHilbert.Parameter.smoothHilbertParameter S n P).hom j)
    (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).family.inclusion (fst _ _)
    (SmoothHilbert.QuasiProjectivity.smoothHilbertParameterQuasiProjectivePresentation S n P)

def smoothEmbeddedGraphParameterHilbertMap : smoothEmbeddedGraphParameter j P ⟶ SmoothHilbert.Parameter.smoothHilbertParameter S n P :=
  Graph.LocusUniversalMorphism.graphLocusBaseMap (SmoothHilbert.Parameter.smoothHilbertParameter S n P)
    (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding (SmoothHilbert.Parameter.smoothHilbertParameter S n P).hom j)
    (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).family.inclusion

def smoothEmbeddedGraphUniversalMorphism :
    (Over.pullback (smoothEmbeddedGraphParameter j P).hom).obj A ⟶
      (Over.pullback (smoothEmbeddedGraphParameter j P).hom).obj B :=
  HilbertConstruction.Over.BaseMapPullback.overBaseMapPullbackMorphism (smoothEmbeddedGraphParameterHilbertMap j P)
    (Graph.LocusUniversalMorphism.graphLocusUniversalMorphism (SmoothHilbert.Parameter.smoothHilbertParameter S n P)
      (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding (SmoothHilbert.Parameter.smoothHilbertParameter S n P).hom j)
      (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).family.inclusion)

def smoothEmbeddedGraphParameterPointEquiv (T : Over S) :
    (T ⟶ smoothEmbeddedGraphParameter j P) ≃
      {c : T ⟶ SmoothHilbert.Parameter.smoothHilbertParameter S n P //
        FactorizationPointCondition.HasIsomorphicFactorization (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding (SmoothHilbert.Parameter.smoothHilbertParameter S n P).hom j)
          (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).family.inclusion
          (fst ((Over.pullback (SmoothHilbert.Parameter.smoothHilbertParameter S n P).hom).obj A)
            ((Over.pullback (SmoothHilbert.Parameter.smoothHilbertParameter S n P).hom).obj B)) c.left} :=
  IsomorphicFactorizationPoints.isomorphicFactorizationPointEquiv (SmoothHilbert.Parameter.smoothHilbertParameter S n P)
    (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding (SmoothHilbert.Parameter.smoothHilbertParameter S n P).hom j)
    (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).family.inclusion (fst _ _) T

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.EmbeddedGraphParameters

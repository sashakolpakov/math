import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.EmbeddedGraphParameters

/-! # Parameter Point Projection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ParameterPointProjection

noncomputable section

/-! The graph parameter embeds monomorphically in its Hilbert base, and the point equivalence preserves that actual projection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

instance graphLocusBaseMap_mono
    {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left] {X P A B : Over M.left}
    [IsProper X.hom] [Flat X.hom] [IsProper A.hom]
    (j : A ⊗ B ⟶ P) [IsClosedImmersion j.left] (i : X ⟶ P) : Mono (LocusUniversalMorphism.graphLocusBaseMap M j i) := by
  have : Mono (FactorizationIsomorphismParameter.factorizationIsomorphismParameterInclusion M j i (fst A B)) := Over.mono_of_mono_left _
  have : Mono (Proper.FactorizationParameter.properFactorizationParameterInclusion M j i) := Over.mono_of_mono_left _
  change Mono (FactorizationIsomorphismParameter.factorizationIsomorphismParameterInclusion M j i (fst A B) ≫ Proper.FactorizationParameter.properFactorizationParameterInclusion M j i)
  infer_instance

local instance graphProjectionPullbackProper {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [IsProper A.hom] :
    IsProper ((Over.pullback f).obj A).hom := inferInstanceAs (IsProper (Limits.pullback.snd A.hom f))

variable {S : Scheme.{u}} [IsNoetherian S] {A B : Over S} {n : ℕ} [IsProper A.hom]
variable (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)

instance smoothEmbeddedGraphParameterHilbertMap_mono : Mono (Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameterHilbertMap j P) :=
  graphLocusBaseMap_mono (SmoothHilbert.Parameter.smoothHilbertParameter S n P)
    (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding (SmoothHilbert.Parameter.smoothHilbertParameter S n P).hom j)
    (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).family.inclusion

theorem smoothEmbeddedGraphParameterPointEquiv_val (T : Over S) (y : T ⟶ Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P) :
    (Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameterPointEquiv j P T y).val = y ≫ Smooth.EmbeddedGraphParameters.smoothEmbeddedGraphParameterHilbertMap j P :=
  (IsomorphicFactorizationPoints.isomorphicFactorizationPointEquiv_val (SmoothHilbert.Parameter.smoothHilbertParameter S n P)
    (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding (SmoothHilbert.Parameter.smoothHilbertParameter S n P).hom j)
    (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).family.inclusion (fst _ _) T y).trans (Category.assoc y _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ParameterPointProjection

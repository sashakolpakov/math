import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Projective Closed Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProjectiveClosedModel

noncomputable section

/-! A smooth noetherian projective closed model includes its actual embedding and recovery isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

structure SmoothProjectiveClosedModel {S T : Scheme.{u}} (X : Over S) (c : T ⟶ S) where
  scheme : Over S
  smooth : Smooth scheme.hom
  noetherian : IsNoetherian scheme.left
  projective : Projective.ProjectivePresentations.ProjectivePresentation scheme
  embedding : scheme ⟶ X
  closed : IsClosedImmersion embedding.left
  recovered : IsIso ((Over.pullback c).map embedding)

def SmoothProjectiveClosedModel.transport {S T : Scheme.{u}} {X X' : Over S} {c : T ⟶ S}
    (L : SmoothProjectiveClosedModel X c) (e : X ≅ X') : SmoothProjectiveClosedModel X' c := by
  have : IsClosedImmersion L.embedding.left := L.closed
  have : IsClosedImmersion e.hom.left := Grassmann.ProjectivePresentation.overIso_closedImmersion e
  have : IsIso ((Over.pullback c).map L.embedding) := L.recovered
  refine {
    scheme := L.scheme
    smooth := L.smooth
    noetherian := L.noetherian
    projective := L.projective
    embedding := L.embedding ≫ e.hom
    closed := ?_
    recovered := ?_ }
  · change IsClosedImmersion (L.embedding.left ≫ e.hom.left)
    exact IsClosedImmersion.comp _ _
  · rw [Functor.map_comp]
    infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProjectiveClosedModel

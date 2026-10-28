import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProjectiveClosedModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.RingMapBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.Families

/-! # Model Projective Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth

noncomputable section

/-! A smooth closed model of a projective coefficient scheme inherits the prescribed finite-dimensional projective embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {C K R : CommRingCat.{u}} (φ : C ⟶ K) (r : Spec R ⟶ Spec K)
variable {X : Over (Spec C)} {n : ℕ} (i : X ⟶ Projective.ProjectivePresentations.affineProjectiveSpace C n) [IsClosedImmersion i.left]
variable (L : ProjectiveClosedModel.SmoothProjectiveClosedModel ((Over.pullback (Spec.map φ)).obj X) r)

def ProjectiveClosedModel.SmoothProjectiveClosedModel.prescribedEmbedding : L.scheme ⟶ Projective.ProjectivePresentations.affineProjectiveSpace K n :=
  L.embedding ≫ (Over.pullback (Spec.map φ)).map i ≫ (Projective.RingMapBaseChange.polynomialProjectiveBaseChangeIso φ n).inv

theorem ProjectiveClosedModel.SmoothProjectiveClosedModel.prescribedEmbedding_closed : IsClosedImmersion (L.prescribedEmbedding φ r i).left := by
  have : IsClosedImmersion L.embedding.left := L.closed
  have : IsClosedImmersion ((Over.pullback (Spec.map φ)).map i).left := Projective.PresentationBaseChange.overPullback_map_closed i (Spec.map φ)
  have : IsClosedImmersion (Projective.RingMapBaseChange.polynomialProjectiveBaseChangeIso φ n).inv.left :=
    Grassmann.ProjectivePresentation.overIso_closedImmersion (Projective.RingMapBaseChange.polynomialProjectiveBaseChangeIso φ n).symm
  change IsClosedImmersion (L.embedding.left ≫ ((Over.pullback (Spec.map φ)).map i).left ≫
    (Projective.RingMapBaseChange.polynomialProjectiveBaseChangeIso φ n).inv.left)
  infer_instance

def ProjectiveClosedModel.SmoothProjectiveClosedModel.prescribedClosedFamily : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace K n) := by
  have : Smooth L.scheme.hom := L.smooth
  have : IsClosedImmersion (L.prescribedEmbedding φ r i).left := L.prescribedEmbedding_closed φ r i
  exact Closed.Families.FlatClosedFamily.ofEmbedding (L.prescribedEmbedding φ r i)

def ProjectiveClosedModel.SmoothProjectiveClosedModel.prescribedClosedFamilyIso : L.scheme ≅ (L.prescribedClosedFamily φ r i).scheme := by
  have : Smooth L.scheme.hom := L.smooth
  have : IsClosedImmersion (L.prescribedEmbedding φ r i).left := L.prescribedEmbedding_closed φ r i
  exact Closed.Families.FlatClosedFamily.ofEmbeddingIso (L.prescribedEmbedding φ r i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth

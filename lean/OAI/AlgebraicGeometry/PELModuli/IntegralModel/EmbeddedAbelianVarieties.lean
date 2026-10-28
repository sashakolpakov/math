import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientModels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.FamilyDimension
import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality
import OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Embedded Abelian Varieties -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.EmbeddedAbelianVarieties

noncomputable section

/-! Turn the constructed embedded complex group fiber into the exact
abelian-variety domain used by Construction, without replacing its scheme or group law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem affineProjectiveSpace_complex (m : ℕ) :
    AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace ℂ m = Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) := rfl

def abelianVariety_projectiveEmbedding (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    A.toOver ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace ℂ A.variety.presentation.ambientDimension :=
  A.variety.presentation.projective.toOverHom

instance abelianVariety_projectiveEmbedding_closed (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    IsClosedImmersion (abelianVariety_projectiveEmbedding A).left :=
  A.variety.presentation.projective.closedImmersion

def embeddedAbelianVariety
    (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [IsProper G.hom] [GeometricallyConnected G.hom]
    (m : ℕ) (i : G ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace ℂ m) [IsClosedImmersion i.left] :
    ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := by
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace_of_subsingleton G.hom
  have hIntegral : IsIntegral G.left := ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction.smooth_connected_scheme_integral G.hom
  let V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation := {
    carrier := G.left
    structureMap := G.hom
    projective := {
      ambientDimension := m
      embedding := i.left
      closedImmersion := inferInstanceAs (IsClosedImmersion i.left)
      over_base := i.w }
    smooth := inferInstance }
  exact {
    variety := ⟨V, hIntegral⟩
    group := inferInstanceAs (GrpObj G)
    commutative := inferInstanceAs (IsCommMonObj G) }

theorem embeddedAbelianVariety_toOver
    (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [IsProper G.hom] [GeometricallyConnected G.hom]
    (m : ℕ) (i : G ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace ℂ m) [IsClosedImmersion i.left] :
    (embeddedAbelianVariety G m i).toOver = G := rfl

theorem embeddedAbelianVariety_dimension
    (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [IsProper G.hom] [GeometricallyConnected G.hom]
    (m : ℕ) (i : G ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace ℂ m) [IsClosedImmersion i.left] :
    topologicalKrullDim G.left =
      (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (embeddedAbelianVariety G m i).variety.structureMap : WithBot ℕ∞) := by
  have : Smooth (embeddedAbelianVariety G m i).toOver.hom := inferInstanceAs (Smooth G.hom)
  have : IsProper (embeddedAbelianVariety G m i).toOver.hom := inferInstanceAs (IsProper G.hom)
  have : GeometricallyConnected (embeddedAbelianVariety G m i).toOver.hom :=
    inferInstanceAs (GeometricallyConnected G.hom)
  have : IsIntegral (embeddedAbelianVariety G m i).toOver.left :=
    (embeddedAbelianVariety G m i).variety.property
  exact Group.FamilyDimension.group_krullDim_eq_transcendenceDimension (embeddedAbelianVariety G m i).toOver

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.EmbeddedAbelianVarieties

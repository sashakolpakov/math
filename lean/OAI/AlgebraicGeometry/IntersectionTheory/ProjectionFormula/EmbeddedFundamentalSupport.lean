import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.EmbeddingCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.Multiplicity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.Fundamental

/-! # Embedded Fundamental Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EmbeddedFundamentalSupport

noncomputable section

/-! The actual embedded fundamental support of an integral smooth
presentation has codimension N minus its smooth dimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

def embedding (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    X.toOver ⟶ (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).toOver :=
  Over.homMk X.embedding X.embedding_over

instance (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) : IsClosedImmersion (EmbeddedFundamentalSupport.embedding X).left :=
  inferInstanceAs (IsClosedImmersion X.embedding)

theorem imageSupport_eq (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W : IrreducibleCloseds X.carrier) :
    ProperCycleLinearity.imageSupport (EmbeddedFundamentalSupport.embedding X) W = Cone.Multiplicity.IntegralProjection.imageSupport X W := rfl

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]

theorem image_whole : ProperCycleLinearity.imageSupport (EmbeddedFundamentalSupport.embedding X) (Integral.Fundamental.whole X) =
    Closed.ImmersionSupport.support X.embedding := by
  apply irreducibleSetEquivPoints.injective
  change CycleClass.Thom.IntersectionGeometry.supportPoint (ProperCycleLinearity.imageSupport (EmbeddedFundamentalSupport.embedding X) (Integral.Fundamental.whole X)) = _
  rw [imageSupport_eq, Cone.Multiplicity.IntegralProjection.image_point,
    Integral.Fundamental.whole_point]
  exact (Closed.ImmersionSupport.support_point X.embedding).symm

theorem codimension (m : ℕ) [SmoothOfRelativeDimension m X.structureMap] :
    (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).supportCodimension
      (Closed.ImmersionSupport.support X.embedding) + m = X.ambientDimension := by
  have he := Closed.EmbeddingCycle.image_codimension (EmbeddedFundamentalSupport.embedding X) m X.ambientDimension
    (Integral.Fundamental.whole X)
  rw [image_whole, Integral.Fundamental.whole_codimension X m, zero_add] at he
  exact he

theorem dimension_le (m : ℕ) [SmoothOfRelativeDimension m X.structureMap] : m ≤ X.ambientDimension := by
  have he := codimension X m
  omega

def support (m : ℕ) [SmoothOfRelativeDimension m X.structureMap] :
    (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).DimensionCycleSupport (X.ambientDimension - m) :=
  ⟨Closed.ImmersionSupport.support X.embedding, by have he := codimension X m; omega⟩

theorem support_range (m : ℕ) [SmoothOfRelativeDimension m X.structureMap] :
    ((support X m).val : Set (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).carrier) =
      Set.range X.embedding := by
  change (CycleClass.Geometric.StratumClosure.integralImageClosure X.embedding : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) = _
  rw [CycleClass.Geometric.StratumClosure.integralImageClosure_coe, X.embedding.isClosedEmbedding.isClosed_range.closure_eq]

theorem degree (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap] :
    p + X.ambientDimension = (p + (X.ambientDimension - m)) + m := by
  have hm := dimension_le X m
  omega

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EmbeddedFundamentalSupport

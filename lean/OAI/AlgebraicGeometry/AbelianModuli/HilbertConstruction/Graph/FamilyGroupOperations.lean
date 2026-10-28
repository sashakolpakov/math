import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresentedGroupGraphBounds
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.EmbeddedGroupGraphBounds
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.EmbeddingClassifier

/-! # Family Group Operations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The ideal-defined Hilbert family of a graph-power embedding carries
the original commutative-group operations through its recovery iso. Its
native addition and inversion graph embeddings retain the uniform bounds. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)

local instance PolarizationData.PolarizedAbelianWithFullLevel.graphOperationSourceFlat : Flat (Over.mk A.abelian.scheme.hom).hom :=
  inferInstanceAs (Flat A.abelian.scheme.hom)
local instance PolarizationData.PolarizedAbelianWithFullLevel.graphOperationSourceFinitePresentation :
    LocallyOfFinitePresentation (Over.mk A.abelian.scheme.hom).hom :=
  inferInstanceAs (LocallyOfFinitePresentation A.abelian.scheme.hom)

instance PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEmbeddingHilbertFamily_proper :
    IsProper (A.graphPowerEmbeddingHilbertFamily hg hN hunit E).family.scheme.hom :=
  (A.graphPowerEmbeddingHilbertFamily hg hN hunit E).family.proper

instance PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEmbeddingHilbertFamily_smooth :
    Smooth (A.graphPowerEmbeddingHilbertFamily hg hN hunit E).family.scheme.hom := by
  let : SmoothOfRelativeDimension g
      (A.graphPowerEmbeddingHilbertFamily hg hN hunit E).family.scheme.hom :=
    A.graphPowerEmbeddingHilbertFamily_dimension hg hN hunit E
  exact SmoothOfRelativeDimension.smooth g _

def PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEmbeddingHilbertPresentation :
    Projective.ProjectivePresentations.ProjectivePresentation (A.graphPowerEmbeddingHilbertFamily hg hN hunit E).family.scheme where
  dimension := E.dimension
  embedding := (A.graphPowerEmbeddingHilbertFamily hg hN hunit E).family.inclusion
  closedImmersion := inferInstance

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEmbeddingHilbertSchemeIso_embedding :
    (A.graphPowerEmbeddingHilbertSchemeIso hg hN hunit E).hom ≫
      (A.graphPowerEmbeddingHilbertPresentation hg hN hunit E).embedding = E.projectivePresentation.embedding := by
  let : IsClosedImmersion
      (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom E.sections E.covers).left := E.closedImmersion
  exact Closed.Families.FlatClosedFamily.ofEmbeddingIso_inclusion
    (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom E.sections E.covers)

def PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEmbeddingHilbertOperations :
    FamilyGroup.Operations.FamilyGroupOperations (A.graphPowerEmbeddingHilbertFamily hg hN hunit E).family.scheme :=
  (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj A.abelian.scheme).ofIso
    (A.graphPowerEmbeddingHilbertSchemeIso hg hN hunit E)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEmbeddingHilbertOperations_laws :
    (A.graphPowerEmbeddingHilbertOperations hg hN hunit E).Laws :=
  (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj A.abelian.scheme).ofIso_laws
    (A.graphPowerEmbeddingHilbertSchemeIso hg hN hunit E)
      (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj_laws A.abelian.scheme)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphPowerEmbeddingHilbertOperations_bounds
    (hd : E.degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) :
    (A.graphPowerEmbeddingHilbertOperations hg hN hunit E).ProjectiveGraphBounds
      (A.graphPowerEmbeddingHilbertPresentation hg hN hunit E)
      (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ) := by
  let : IsClosedImmersion
      (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom E.sections E.covers).left := E.closedImmersion
  let : IsClosedImmersion
      (A.graphPowerEmbeddingHilbertPresentation hg hN hunit E).embedding.left :=
    (A.graphPowerEmbeddingHilbertPresentation hg hN hunit E).closedImmersion
  exact FamilyGroup.Operations.FamilyGroupOperations.ProjectiveGraphBounds.ofIso
    E.projectivePresentation.embedding (A.graphPowerEmbeddingHilbertPresentation hg hN hunit E).embedding
    (A.graphPowerEmbeddingHilbertSchemeIso hg hN hunit E)
    (A.graphPowerEmbeddingHilbertSchemeIso_embedding hg hN hunit E)
    (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj A.abelian.scheme)
    (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
    (A.uniformEmbeddedGroupGraphBounds hg hN hunit E hd)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

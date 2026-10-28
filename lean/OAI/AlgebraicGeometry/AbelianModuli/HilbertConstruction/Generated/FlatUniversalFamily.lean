import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GeneratedFamily

/-! # Flat Universal Family -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.FlatUniversalFamily

noncomputable section

/-! An actual flat finitely presented closed universal family over the generated parameter locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (S : Scheme.{u}) (n B : ℕ) (r : ℕ → ℕ) (N : ℕ)
variable (hB : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B)

def generatedFlatUniversalFamily :
    Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N).left n) := by
  let F := Truncated.GeneratedFamily.truncatedGeneratedFamily S n B r N
  let j : F ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N).left n :=
    (Truncated.GeneratedFamily.truncatedGeneratedProjectivePresentation S n B r N).embedding
  have : Flat F.hom := Truncated.GeneratedFamily.truncatedGeneratedFamily_flat hB
  have : LocallyOfFinitePresentation F.hom := Truncated.GeneratedFamily.truncatedGeneratedFamily_locallyFinitePresentation S n B r N
  have : IsClosedImmersion j.left :=
    (Truncated.GeneratedFamily.truncatedGeneratedProjectivePresentation S n B r N).closedImmersion
  exact Closed.Families.FlatClosedFamily.ofEmbedding j

def generatedFlatUniversalFamilyIso :
    Truncated.GeneratedFamily.truncatedGeneratedFamily S n B r N ≅ (generatedFlatUniversalFamily S n B r N hB).scheme := by
  let F := Truncated.GeneratedFamily.truncatedGeneratedFamily S n B r N
  let j : F ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N).left n :=
    (Truncated.GeneratedFamily.truncatedGeneratedProjectivePresentation S n B r N).embedding
  have : Flat F.hom := Truncated.GeneratedFamily.truncatedGeneratedFamily_flat hB
  have : LocallyOfFinitePresentation F.hom := Truncated.GeneratedFamily.truncatedGeneratedFamily_locallyFinitePresentation S n B r N
  have : IsClosedImmersion j.left :=
    (Truncated.GeneratedFamily.truncatedGeneratedProjectivePresentation S n B r N).closedImmersion
  exact Closed.Families.FlatClosedFamily.ofEmbeddingIso j

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.FlatUniversalFamily

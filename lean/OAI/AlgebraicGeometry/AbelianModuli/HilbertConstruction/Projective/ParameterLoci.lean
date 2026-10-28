import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations

/-! # Parameter Loci -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective

noncomputable section

/-!
Projective presentations pass to closed parameter loci. Quasi-compact open
parts of these loci have actual quasi-projective presentations over the base.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {X Y : Over S}

def ProjectivePresentations.ProjectivePresentation.ofClosedImmersion (P : ProjectivePresentations.ProjectivePresentation X)
    (j : Y ⟶ X) [IsClosedImmersion j.left] : ProjectivePresentations.ProjectivePresentation Y where
  dimension := P.dimension
  embedding := j ≫ P.embedding
  closedImmersion := IsClosedImmersion.comp j.left P.embedding.left

def ProjectivePresentations.ProjectivePresentation.quasiProjectiveOpen (P : ProjectivePresentations.ProjectivePresentation X)
    (j : Y ⟶ X) [IsOpenImmersion j.left] [QuasiCompact j.left] :
    ProjectivePresentations.QuasiProjectivePresentation Y where
  locallyFiniteType := by
    have : IsProper X.hom := P.proper
    rw [← j.w]
    infer_instance
  quasiCompact := by
    have : IsProper X.hom := P.proper
    rw [← j.w]
    infer_instance
  compactification := X
  projective := P
  embedding := j
  openImmersion := inferInstance

def ProjectivePresentations.ProjectivePresentation.quasiProjective (P : ProjectivePresentations.ProjectivePresentation X) :
    ProjectivePresentations.QuasiProjectivePresentation X := by
  have : IsOpenImmersion (𝟙 X : X ⟶ X).left :=
    inferInstanceAs (IsOpenImmersion (𝟙 X.left))
  have : QuasiCompact (𝟙 X : X ⟶ X).left :=
    inferInstanceAs (QuasiCompact (𝟙 X.left))
  exact P.quasiProjectiveOpen (𝟙 X)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective

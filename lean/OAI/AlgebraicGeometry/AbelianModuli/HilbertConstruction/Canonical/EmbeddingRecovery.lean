import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresentationSourceTransport

/-! # Embedding Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.EmbeddingRecovery

noncomputable section

/-! An isomorphism intertwining two actual embeddings preserves the
complete canonical coordinate-section condition. This transfers complete
local graph embeddings to their native Hilbert-family recoveries. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} {X Y : Over S} {n : ℕ}
variable (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (j : Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
variable [IsClosedImmersion i.left] [IsClosedImmersion j.left]
variable (e : X ≅ Y) (h : e.hom ≫ j = i)

def completeCanonicalData_of_embeddingIso
    (C : (⟨n, i, inferInstance⟩ : Projective.ProjectivePresentations.ProjectivePresentation X).canonicalSectionData.CompleteData) :
    (⟨n, j, inferInstance⟩ : Projective.ProjectivePresentations.ProjectivePresentation Y).canonicalSectionData.CompleteData := by
  letI : IsClosedImmersion e.inv.left := Grassmann.ProjectivePresentation.overIso_closedImmersion e.symm
  let P : Projective.ProjectivePresentations.ProjectivePresentation X := ⟨n, i, inferInstance⟩
  let Q : Projective.ProjectivePresentations.ProjectivePresentation Y := ⟨n, j, inferInstance⟩
  let D := P.canonicalSectionData.precomp e.inv
  let C' := C.precompIso e.symm
  have hi : e.inv ≫ i = j :=
    (congrArg (fun a => e.inv ≫ a) h.symm).trans (Iso.inv_hom_id_assoc e j)
  let E : Q.SectionData (P.ampleLineBundle.pullback e.inv.left) := {
    sections := D.sections
    covers := D.covers
    embedding_eq := hi.symm.trans D.embedding_eq }
  let CE : E.CompleteData := ⟨C'.basis, C'.sections_eq⟩
  exact Projective.ProjectivePresentations.ProjectivePresentation.SectionData.CompleteData.canonical E CE

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.EmbeddingRecovery

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresentationSectionData

/-! # Power Embedding Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A power embedding can use its canonical tensor-power sheaf while
retaining the original embedding and complete section basis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {X : Over S} {L : Line.Bundles.LineBundle X.left}
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom) (d : ℕ) (hd : E.degree = d)

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.canonicalDegreeIso : E.power.sheaf ≅ (L.tensorPower d).sheaf :=
  (E.isPower.unique (L.tensorPower_isTensorPower E.degree)).some ≪≫
    eqToIso (congrArg (fun k => (L.tensorPower k).sheaf) hd)

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.canonicalDegree : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom where
  degree := d
  degree_pos := hd ▸ E.degree_pos
  power := L.tensorPower d
  isPower := L.tensorPower_isTensorPower d
  dimension := E.dimension
  sections := (E.sectionData.ofBundleIso (E.canonicalDegreeIso d hd)).sections
  covers := (E.sectionData.ofBundleIso (E.canonicalDegreeIso d hd)).covers
  closedImmersion := by
    have h := congrArg
      (fun a : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S E.dimension => IsClosedImmersion a.left)
      (E.sectionData.ofBundleIso (E.canonicalDegreeIso d hd)).embedding_eq
    exact h.mp E.closedImmersion

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.canonicalDegree_embedding :
    (E.canonicalDegree d hd).projectivePresentation.embedding = E.projectivePresentation.embedding :=
  (E.sectionData.ofBundleIso (E.canonicalDegreeIso d hd)).embedding_eq.symm

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.CompleteSectionData.canonicalDegreeData (C : E.CompleteSectionData) :
    (E.canonicalDegree d hd).CompleteSectionData := by
  let D := (C.presentationCompleteData E).ofBundleIso (E.canonicalDegreeIso d hd)
  exact ⟨D.basis, D.sections_eq⟩

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.HasCompleteSections.canonicalDegree (h : E.HasCompleteSections) :
    (E.canonicalDegree d hd).HasCompleteSections :=
  ⟨h.some.canonicalDegreeData E d hd⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

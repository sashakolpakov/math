import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ChowModificationModel
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionCoverProjective

/-! # Projective Chow Modification -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent

noncomputable section

/-! Chow modifications equipped with an actual closed embedding into one
finite-dimensional projective space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}

def ChowModificationModel.Construction.ChowModification.Model.sectionCover (D : ChowModificationModel.Construction.ChowModification.Model f) : AffineSectionOf.Construction.AffineSectionCover.Data D.scheme := by
  let C (i : Fin D.cover.n) : AffineSectionOf.Construction.AffineSectionCover.Data (D.compactification i).scheme := by
    have : IsClosedImmersion (D.compactification i).embedding :=
      (D.compactification i).closedImmersion
    exact (ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionCover
      (R := R) (none : Option (Fin (D.compactification i).n))).pullback
        (D.compactification i).embedding
  have : IsClosedImmersion D.embedding := D.closedImmersion
  exact (AffineSectionOf.Construction.AffineSectionCover.finiteProduct
    (fun i => Over.mk (D.compactification i).base) C).pullback D.embedding

def ChowModificationModel.Construction.ChowModification.Model.projectivePresentation (D : ChowModificationModel.Construction.ChowModification.Model f) [IsProper f] :
    AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (D.projection ≫ f)) := by
  have : IsProper D.projection := D.proper
  exact D.sectionCover.projectivePresentation (D.projection ≫ f)

/-- Every proper integral scheme over a Noetherian affine base has a
proper surjective integral modification, an isomorphism over a nonempty
affine open, whose source is projective over the original base. -/
theorem ProjectiveChowModification.Construction.ChowModification.exists_projective_modification [IsNoetherianRing R] [IsIntegral X]
    (f : X ⟶ Spec (.of R)) [IsProper f] :
    ∃ (Z : Scheme.{u}) (_ : IsIntegral Z) (q : Z ⟶ X),
      IsProper q ∧ Surjective q ∧
      (∃ U : X.Opens, Nonempty U ∧ IsAffineOpen U ∧ IsIso (q ∣_ U)) ∧
      Nonempty (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (q ≫ f))) := by
  let D := ChowModificationModel.Construction.ChowModification.build f
  exact ⟨D.scheme, D.integral, D.projection, D.proper, D.surjective,
    ⟨D.cover.common, D.cover.common_nonempty, D.cover.common_affine, D.isIso_restrict⟩,
    ⟨D.projectivePresentation⟩⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent

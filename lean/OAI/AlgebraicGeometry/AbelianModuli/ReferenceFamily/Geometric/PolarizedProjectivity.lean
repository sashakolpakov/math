import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ProjectivePresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.BaseChangeCoherence

/-! # Polarized Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.PolarizedProjectivity

noncomputable section

/-! The actual polarization supplies a projective embedding over any
algebraically closed field, before choosing a complex embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

theorem geometricPolarization_has_ample_line_bundle :
    ∃ L : HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left, L.IsAmple := by
  obtain ⟨L, hL, _⟩ := A.polarization.positive k (𝟙 (Spec (.of k)))
  let f := A.abelian.pullbackIdIso.inv.left
  let : IsIso f := inferInstanceAs
    (IsIso (((Over.forget (Spec (.of k))).mapIso A.abelian.pullbackIdIso).inv))
  exact ⟨L.pullback f, hL.pullback_of_isIso f⟩

def geometricPolarizedProjectivePresentation : HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.abelian.scheme := by
  let L := Classical.choose (geometricPolarization_has_ample_line_bundle A)
  have hL : L.IsAmple := Classical.choose_spec (geometricPolarization_has_ample_line_bundle A)
  exact hL.projectivePresentation A.abelian.scheme.hom

def geometricPolarizedProjectiveEmbedding :
    A.abelian.scheme ⟶ HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace k (geometricPolarizedProjectivePresentation A).dimension :=
  (geometricPolarizedProjectivePresentation A).embedding ≫
    (HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of k) (geometricPolarizedProjectivePresentation A).dimension).hom

instance geometricPolarizedProjectiveEmbedding_closed :
    IsClosedImmersion (geometricPolarizedProjectiveEmbedding A).left := by
  have : IsIso (HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of k)
      (geometricPolarizedProjectivePresentation A).dimension).hom.left :=
    ((Over.forget (Spec (.of k))).mapIso
      (HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of k) (geometricPolarizedProjectivePresentation A).dimension)).isIso_hom
  exact inferInstanceAs (IsClosedImmersion
    ((geometricPolarizedProjectivePresentation A).embedding.left ≫
      (HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of k) (geometricPolarizedProjectivePresentation A).dimension).hom.left))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.PolarizedProjectivity

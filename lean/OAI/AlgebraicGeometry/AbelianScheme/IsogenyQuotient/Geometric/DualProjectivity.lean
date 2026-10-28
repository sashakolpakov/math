import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.AbelianModel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AmpleAffinePullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyComplementGeometry
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PolarizationEtale

/-! # Dual Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.DualProjectivity.Construction

noncomputable section

/-! The original dual of a polarized abelian variety is projective over
every algebraically closed characteristic-zero field. The complementary
isogeny pulls back an ample line from the original abelian variety. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

theorem geometricDual_has_ample_line_bundle :
    ∃ L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.dual.abelian.scheme.left, L.IsAmple := by
  have : Etale A.polarization.isogeny.hom.left :=
    CentralAction.PolarizationEtale.Construction.polarization_etale A.polarization.isogeny δ A.polarization.kernelType
  obtain ⟨_, q, _, _, hq, _, _, _, _, _⟩ :=
    PELModuli.IntegralModel.IsogenyComplementGeometry.exists_complementary_finite_etale_isogeny A.polarization.isogeny.hom
  have : IsFinite q.left := hq
  have : CompactSpace A.dual.abelian.scheme.left :=
    QuasiCompact.compactSpace_of_compactSpace A.dual.abelian.scheme.hom
  obtain ⟨L, hL⟩ := AbelianModuli.ReferenceFamily.Geometric.PolarizedProjectivity.geometricPolarization_has_ample_line_bundle A
  exact ⟨L.pullback q.left, AbelianModuli.ReferenceFamily.AmpleAffinePullback.ample_pullback_affine q.left L hL⟩

def geometricDualProjectivePresentation : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme := by
  let L := (geometricDual_has_ample_line_bundle A).choose
  have hL : L.IsAmple := (geometricDual_has_ample_line_bundle A).choose_spec
  exact hL.projectivePresentation A.dual.abelian.scheme.hom

def geometricDualProjectiveEmbedding :
    A.dual.abelian.scheme ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace k (geometricDualProjectivePresentation A).dimension :=
  (geometricDualProjectivePresentation A).embedding ≫
    (AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of k) (geometricDualProjectivePresentation A).dimension).hom

instance geometricDualProjectiveEmbedding_closed :
    IsClosedImmersion (geometricDualProjectiveEmbedding A).left := by
  have : IsIso (AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of k)
      (geometricDualProjectivePresentation A).dimension).hom.left :=
    ((Over.forget (Spec (.of k))).mapIso
      (AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of k) (geometricDualProjectivePresentation A).dimension)).isIso_hom
  change IsClosedImmersion ((geometricDualProjectivePresentation A).embedding.left ≫
    (AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of k) (geometricDualProjectivePresentation A).dimension).hom.left)
  infer_instance

theorem geometricDual_has_group_model :
    Nonempty (AbelianModuli.ReferenceFamily.Geometric.GroupModel.GeometricGroupModel A.dual.abelian.scheme
      (geometricDualProjectivePresentation A).dimension) := by
  have : IsIntegral A.dual.abelian.scheme.left :=
    Picard.Homomorphisms.GroupRigidity.Construction.integral_smooth_proper_connected_group A.dual.abelian.scheme
  exact AbelianModuli.ReferenceFamily.Geometric.GroupModel.exists_geometric_group_model A.dual.abelian.scheme _ (geometricDualProjectiveEmbedding A)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.DualProjectivity.Construction

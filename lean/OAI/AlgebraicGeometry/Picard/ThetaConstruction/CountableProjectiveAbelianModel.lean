import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.Models
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange
import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupRigidity
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CountableComplexEmbedding

/-! # Countable Projective Abelian Model -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.CountableProjectiveAbelianModel.Geometric

noncomputable section

/-! Every projectively presented abelian scheme over an algebraically
closed characteristic-zero field has an actual countable algebraically
closed group model, and that field embeds in the complex numbers.
No dual abelian scheme is an input. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.Models.Construction

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))

theorem exists_countable_projective_abelian_model
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.scheme) :
    ∃ F : Subfield k, Countable F ∧ IsAlgClosed F ∧ Nonempty (F →+* ℂ) ∧
      ∃ B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of F)),
        ∃ e : A.scheme ≅ (B.pullback (Spec.map (CommRingCat.ofHom F.subtype))).scheme,
          IsMonHom e.hom := by
  let i : A.scheme ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace k P.dimension :=
    P.embedding ≫ (AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of k) P.dimension).hom
  let : IsClosedImmersion (AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of k) P.dimension).hom.left :=
    inferInstanceAs (IsClosedImmersion
      (((Over.forget (Spec (.of k))).mapIso (AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of k) P.dimension)).hom))
  let : IsClosedImmersion i.left := IsClosedImmersion.comp P.embedding.left _
  let : IsIntegral A.scheme.left := Homomorphisms.GroupRigidity.Construction.integral_smooth_proper_connected_group A.scheme
  obtain ⟨D⟩ := AbelianModuli.ReferenceFamily.Geometric.GroupModel.exists_geometric_group_model A.scheme P.dimension i
  obtain ⟨M⟩ := AbelianScheme.IsogenyQuotient.Countable.Models.Construction.countable_abelian_family_model_exists
    (fun _ : Unit => g) (fun _ => A) (fun _ => P.dimension) (fun _ => D)
  exact ⟨M.field, inferInstance, inferInstance,
    AbelianScheme.TateComparison.CountableComplexEmbedding.countable_field_has_complex_embedding M.field,
    M.family (), M.recovery (), M.recovery_group ()⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.CountableProjectiveAbelianModel.Geometric

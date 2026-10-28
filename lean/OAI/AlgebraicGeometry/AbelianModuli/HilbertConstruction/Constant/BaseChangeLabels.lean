import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Morphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentingIsoPoints

/-! # Base Change Labels -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChangeLabels

noncomputable section

/-! The canonical base-change isomorphism for a constant scheme preserves each actual labeled section. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} (f : T ⟶ S) (I : Type u)

theorem constantSchemeBaseChangeIso_index (z : (ConstantScheme.Iff.constantScheme T I).left) :
    ConstantScheme.Iff.constantSchemeIndex S I
      (((BaseChange.constantSchemeBaseChangeIso f I).hom.left ≫ pullback.fst (ConstantScheme.Iff.constantScheme S I).hom f) z) =
      ConstantScheme.Iff.constantSchemeIndex T I z := by
  have h := RepresentingIsoPoints.representingIso_homEquiv (BaseChange.constantSetRepresentable T I)
    (BaseChange.constantSetPullbackRepresentable f I) (𝟙 (ConstantScheme.Iff.constantScheme T I))
  rw [Category.id_comp] at h
  exact congrArg (fun a : LocallyConstant (ConstantScheme.Iff.constantScheme T I).left I => a z) h

theorem constantSchemeBaseChangeIso_projection_over :
    ((BaseChange.constantSchemeBaseChangeIso f I).hom.left ≫ pullback.fst (ConstantScheme.Iff.constantScheme S I).hom f) ≫
      (ConstantScheme.Iff.constantScheme S I).hom = (ConstantScheme.Iff.constantScheme T I).hom ≫ f := by
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun a => a ≫ f) (BaseChange.constantSchemeBaseChangeIso f I).hom.w

theorem constantSchemeBaseChangeIso_label_fst (i : I) :
    (ConstantScheme.Morphisms.constantSchemeLabelPoint T I i ≫ (BaseChange.constantSchemeBaseChangeIso f I).hom).left ≫
      pullback.fst (ConstantScheme.Iff.constantScheme S I).hom f = f ≫ (ConstantScheme.Morphisms.constantSchemeLabelPoint S I i).left := by
  let q : T ⟶ (ConstantScheme.Iff.constantScheme S I).left :=
    (ConstantScheme.Morphisms.constantSchemeLabelPoint T I i).left ≫
      (BaseChange.constantSchemeBaseChangeIso f I).hom.left ≫ pullback.fst (ConstantScheme.Iff.constantScheme S I).hom f
  have hq : q ≫ (ConstantScheme.Iff.constantScheme S I).hom = f := by
    change ((ConstantScheme.Morphisms.constantSchemeLabelPoint T I i).left ≫
      ((BaseChange.constantSchemeBaseChangeIso f I).hom.left ≫ pullback.fst (ConstantScheme.Iff.constantScheme S I).hom f)) ≫
        (ConstantScheme.Iff.constantScheme S I).hom = f
    rw [Category.assoc, constantSchemeBaseChangeIso_projection_over, ← Category.assoc]
    exact (congrArg (fun a : T ⟶ T => a ≫ f) (ConstantScheme.Morphisms.constantSchemeLabelPoint T I i).w).trans (Category.id_comp f)
  have hi : ∀ z : T, ConstantScheme.Iff.constantSchemeIndex S I (q z) = i := by
    intro z
    exact (constantSchemeBaseChangeIso_index f I ((ConstantScheme.Morphisms.constantSchemeLabelPoint T I i).left z)).trans
      (ConstantScheme.Iff.constantSchemeIndex_ι i z)
  have h := ConstantScheme.Iff.constantScheme_factor q i hi
  rw [hq] at h
  exact (Category.assoc _ _ _).trans h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChangeLabels

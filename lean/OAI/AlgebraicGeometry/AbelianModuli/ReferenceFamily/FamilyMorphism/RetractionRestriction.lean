import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.ProductRestrictionSquare
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.GroupRetractionRestriction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.GroupRetractions

/-! # Retraction Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.RetractionRestriction

noncomputable section

/-! The actual pulled target retraction commutes with restriction
of both original affine subfamilies. All maps use the original family
morphism and its selected reference product coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver
attribute [local irreducible] ProductCoordinates.familyMorphismProductCoordinates Family.RestrictionCoordinates.familyReferenceRestrictionCoordinates
attribute [local irreducible] Family.CommonOpenGroupRetractions.familyCommonOpenGroupRetraction GroupRetractions.familyMorphismGroupRetraction

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    {X Y : Over (Spec (.of R))} [Smooth X.hom] [Smooth Y.hom]
    (f : X ⟶ Y) (V V' : X.left.affineOpens) (W W' : Y.left.affineOpens)
    (t : V'.1 ≤ V.1) (s : W'.1 ≤ W.1)
    (h : V.1 ≤ f.left ⁻¹ᵁ W.1) (h' : V'.1 ≤ f.left ⁻¹ᵁ W'.1) (d : Derivation ℂ R ℂ)

theorem familyMorphismCoefficient_scheme_square :
    Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V))
        (DualNumber (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V'))
        (Dual.TensorMapCoordinates.dualTensorMapCoordinates (Family.RestrictionCoordinates.familyReferenceRestrictionCoordinates ℂ R X t d)) ≫
      Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W))
        (DualNumber (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V))
        (Dual.TensorMapCoordinates.dualTensorMapCoordinates (ProductCoordinates.familyMorphismProductCoordinates ℂ R f V W h d)) =
    Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W'))
        (DualNumber (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V'))
        (Dual.TensorMapCoordinates.dualTensorMapCoordinates (ProductCoordinates.familyMorphismProductCoordinates ℂ R f V' W' h' d)) ≫
      Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W))
        (DualNumber (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W'))
        (Dual.TensorMapCoordinates.dualTensorMapCoordinates (Family.RestrictionCoordinates.familyReferenceRestrictionCoordinates ℂ R Y s d)) := by
  rw [Affine.OverMorphismAlgebra.affineOverAlgHom_comp, Affine.OverMorphismAlgebra.affineOverAlgHom_comp]
  exact congrArg (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W))
    (DualNumber (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V')))
    (ProductRestrictionSquare.familyMorphismCoefficientCoordinates_square ℂ R f V V' W W' t s h h' d)

theorem familyMorphismGroupRetraction_restrict (Z : Y.left.affineOpens) (j : W.1 ≤ Z.1) :
    Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V))
        (DualNumber (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V'))
        (Dual.TensorMapCoordinates.dualTensorMapCoordinates (Family.RestrictionCoordinates.familyReferenceRestrictionCoordinates ℂ R X t d)) ≫
      (GroupRetractions.familyMorphismGroupRetraction R f V W Z h j d).val =
    (GroupRetractions.familyMorphismGroupRetraction R f V' W' Z h' (s.trans j) d).val := by
  rw [GroupRetractions.familyMorphismGroupRetraction_value, GroupRetractions.familyMorphismGroupRetraction_value,
    ← Category.assoc, familyMorphismCoefficient_scheme_square R f V V' W W' t s h h' d,
    Category.assoc, Family.GroupRetractionRestriction.familyCommonOpenGroupRetraction_restrict]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.RetractionRestriction

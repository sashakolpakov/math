import OAI.RepresentationTheory.Theta.Geometric.DualNumbers
import OAI.RepresentationTheory.Theta.Geometric.DerivationBaseChange

/-! # Affine Tangents -/

namespace OAI.RepresentationTheory.Theta.Geometric.AffineTangents

noncomputable section

/-! Relative spectrum identifies extended-field derivations with the
literal infinitesimal fiber of the affine scheme's point functor. -/

open scoped TensorProduct
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k A F : Type) [Field k] [CommRing A] [Field F]
  [Algebra k A] [Algebra k F] [Algebra A F] [IsScalarTower k A F]

def geometricAffineOrigin : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver k F ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver k (DualNumber F) :=
  AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k (DualNumber F) F (TrivSqZeroExt.fstHom k F F)

def geometricAffineBasePoint : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver k F ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver k A :=
  AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k A F (IsScalarTower.toAlgHom k A F)

def geometricAffineTangentPoints :=
  {f : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver k (DualNumber F) ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver k A //
    geometricAffineOrigin k F ≫ f = geometricAffineBasePoint k A F}

theorem geometricAffineTangent_condition (f : A →ₐ[k] DualNumber F) :
    geometricAffineOrigin k F ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k A (DualNumber F) f =
      geometricAffineBasePoint k A F ↔ ∀ a, (f a).fst = algebraMap A F a := by
  change AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k (DualNumber F) F (TrivSqZeroExt.fstHom k F F) ≫ _ = _ ↔ _
  rw [Affine.Tangents.affineSpec_comp]
  change AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k A F ((TrivSqZeroExt.fstHom k F F).comp f) =
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k A F (IsScalarTower.toAlgHom k A F) ↔ _
  rw [(AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k A F).injective.eq_iff]
  exact ⟨fun h a => congrArg (fun h : A →ₐ[k] F => h a) h, fun h => AlgHom.ext h⟩

def geometricAffineTangentEquiv :
    {f : A →ₐ[k] DualNumber F // ∀ a, (f a).fst = algebraMap A F a} ≃
      geometricAffineTangentPoints k A F where
  toFun f := ⟨AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k A (DualNumber F) f.val,
    (geometricAffineTangent_condition k A F f.val).mpr f.property⟩
  invFun f := ⟨(AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k A (DualNumber F)).symm f.val,
    (geometricAffineTangent_condition k A F _).mp
      (by rw [Equiv.apply_symm_apply]; exact f.property)⟩
  left_inv f := Subtype.ext ((AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k A (DualNumber F)).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k A (DualNumber F)).apply_symm_apply f.val)

def geometricDerivationSpecEquiv : Derivation k A F ≃ geometricAffineTangentPoints k A F :=
  DualNumbers.geometricDerivationJetEquiv.trans (geometricAffineTangentEquiv k A F)

def extendedAffineTangentEquiv [Algebra A k] [IsScalarTower k A k]
    [IsScalarTower A k F] [Algebra.EssFiniteType k A] :
    (F ⊗[k] Derivation k A k) ≃ geometricAffineTangentPoints k A F :=
  (DerivationBaseChange.pointDerivationBaseChange k A F).toEquiv.trans (geometricDerivationSpecEquiv k A F)

variable {k A F}
variable {B : Type} [CommRing B] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  [Algebra B F] [IsScalarTower k B F] [IsScalarTower A B F]

theorem geometricDerivationJet_comap (δ : Derivation k B F) :
    DualNumbers.geometricDerivationJet (DerivationBaseChange.pointDerivationComap k A B F δ) =
      (DualNumbers.geometricDerivationJet δ).comp (IsScalarTower.toAlgHom k A B) := by
  apply AlgHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · exact IsScalarTower.algebraMap_apply A B F a
  · rfl

theorem geometricDerivationSpec_comap (δ : Derivation k B F) :
    (geometricDerivationSpecEquiv k A F (DerivationBaseChange.pointDerivationComap k A B F δ)).val =
      (geometricDerivationSpecEquiv k B F δ).val ≫
        AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k A B (IsScalarTower.toAlgHom k A B) := by
  change AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k A (DualNumber F)
    (DualNumbers.geometricDerivationJet (DerivationBaseChange.pointDerivationComap k A B F δ)) = _
  rw [geometricDerivationJet_comap]
  exact (Affine.Tangents.affineSpec_comp _ _).symm

end

end OAI.RepresentationTheory.Theta.Geometric.AffineTangents

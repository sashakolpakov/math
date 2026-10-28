import OAI.RepresentationTheory.Theta.Geometric.Affine.Tangents

/-! # Tangent Naturality -/

namespace OAI.RepresentationTheory.Theta.Geometric.Affine.TangentNaturality

noncomputable section

/-! The derivation-to-scheme-tangent comparison commutes with the actual
morphism of affine schemes induced by an algebra map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {k R S : Type} [Field k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
  [Algebra R k] [Algebra S k] [IsScalarTower k R k] [IsScalarTower k S k]
  [IsScalarTower R S k]

theorem derivationDualNumber_compAlgebraMap (δ : Derivation k S k) :
    Dual.Numbers.derivationDualNumber (δ.compAlgebraMap R) =
      (Dual.Numbers.derivationDualNumber δ).comp (IsScalarTower.toAlgHom k R S) := by
  apply AlgHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · exact IsScalarTower.algebraMap_apply R S k a
  · rfl

theorem derivationAffineTangent_compAlgebraMap (δ : Derivation k S k) :
    (Tangents.derivationAffineTangentEquiv k R (δ.compAlgebraMap R)).val =
      (Tangents.derivationAffineTangentEquiv k S δ).val ≫
        AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k R S (IsScalarTower.toAlgHom k R S) := by
  change AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k R (DualNumber k)
      (Dual.Numbers.derivationDualNumber (δ.compAlgebraMap R)) = _
  rw [derivationDualNumber_compAlgebraMap]
  exact (Tangents.affineSpec_comp _ _).symm

end

end OAI.RepresentationTheory.Theta.Geometric.Affine.TangentNaturality

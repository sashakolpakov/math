import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualDerivationCoefficientMaps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientLiftNaturality

/-! # Dual Lift Precomposition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftPrecomposition

noncomputable section

/-! Precomposition of affine coordinate algebras gives literal
postcomposition of the actual dual-number scheme lifts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k B D C : Type) [CommRing k] [CommRing B] [CommRing D] [CommRing C]
    [Algebra k B] [Algebra k D] [Algebra k C] [Algebra B D] [Algebra B C] [Algebra D C]
    [IsScalarTower k B D] [IsScalarTower k B C] [IsScalarTower k D C] [IsScalarTower B D C]

theorem affineDualLiftSpaceEquiv_precomposition (v : Dual.AlgebraLiftCoordinates.DualCoefficientLifts.Space C k D) :
    ((DualLiftConormal.affineDualLiftSpaceEquiv k D C).symm v).val ≫ AlgebraAutomorphismNaturality.affineOverAlgHom k B D (IsScalarTower.toAlgHom k B D) =
      ((DualLiftConormal.affineDualLiftSpaceEquiv k B C).symm (Dual.CoefficientLiftNaturality.dualCoefficientLiftPrecomposition k B D C v)).val := by
  apply Over.OverMorphism.ext
  change ((DualLiftConormal.affineDualLiftSpaceEquiv k D C).symm v).val.left ≫
      Spec.map (CommRingCat.ofHom (IsScalarTower.toAlgHom k B D).toRingHom) =
    ((DualLiftConormal.affineDualLiftSpaceEquiv k B C).symm (Dual.CoefficientLiftNaturality.dualCoefficientLiftPrecomposition k B D C v)).val.left
  rw [← DualDerivationCoefficientMaps.affineDualLiftSpaceEquiv_symm_spec, ← DualDerivationCoefficientMaps.affineDualLiftSpaceEquiv_symm_spec, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun b => (Dual.CoefficientLiftNaturality.dualCoefficientLiftPrecomposition_hom k B D C v b).symm)

theorem affineDualLiftDerivationEquiv_precomposition (d : Derivation k D C) :
    ((DualLiftConormal.affineDualLiftDerivationEquiv k D C).symm d).val ≫ AlgebraAutomorphismNaturality.affineOverAlgHom k B D (IsScalarTower.toAlgHom k B D) =
      ((DualLiftConormal.affineDualLiftDerivationEquiv k B C).symm (Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k B D C d)).val := by
  let v := (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C k D).symm d
  have hv : Dual.CoefficientLiftNaturality.dualCoefficientLiftPrecomposition k B D C v =
      (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C k B).symm (Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k B D C d) := by
    change (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C k B).symm
      (Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k B D C (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C k D v)) = _
    rw [LinearEquiv.apply_symm_apply]
  have h := affineDualLiftSpaceEquiv_precomposition k B D C v
  rw [hv] at h
  exact h

theorem affineCoefficientPoint_precomposition :
    AlgebraAutomorphismNaturality.affineOverAlgHom k D C (IsScalarTower.toAlgHom k D C) ≫
      AlgebraAutomorphismNaturality.affineOverAlgHom k B D (IsScalarTower.toAlgHom k B D) =
    AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C) := by
  rw [OverMorphismAlgebra.affineOverAlgHom_comp]
  apply congrArg (AlgebraAutomorphismNaturality.affineOverAlgHom k B C)
  exact AlgHom.ext (fun b => (IsScalarTower.algebraMap_apply B D C b).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftPrecomposition

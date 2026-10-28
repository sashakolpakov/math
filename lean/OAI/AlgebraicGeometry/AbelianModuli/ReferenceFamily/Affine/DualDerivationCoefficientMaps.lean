import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftConormal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientLiftNaturality

/-! # Dual Derivation Coefficient Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualDerivationCoefficientMaps

noncomputable section

section

/-! The actual affine scheme map of a lift changes by the actual
dual-number coefficient map. This identifies the algebraically linear
coefficient operation with literal precomposition of scheme maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k B C : Type) [CommRing k] [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] [Algebra B C] [IsScalarTower k B C]

theorem affineDualLiftSpaceEquiv_symm_spec (v : Dual.AlgebraLiftCoordinates.DualCoefficientLifts.Space C k B) :
    Spec.map (CommRingCat.ofHom v.val.hom) = ((DualLiftConormal.affineDualLiftSpaceEquiv k B C).symm v).val.left := by
  let f := (DualLiftConormal.affineDualLiftSpaceEquiv k B C).symm v
  have h : (OverMorphismAlgebra.affineOverMorphismAlgebra k (DualNumber C) B f.val).toRingHom = v.val.hom := by
    apply RingHom.ext
    intro b
    have hb := congrArg (fun w : Dual.AlgebraLiftCoordinates.DualCoefficientLifts.Space C k B => w.val.hom b)
      ((DualLiftConormal.affineDualLiftSpaceEquiv k B C).apply_symm_apply v)
    exact (DualLiftConormal.affineDualLiftSpaceEquiv_hom k B C f b).symm.trans hb
  rw [← h]
  exact OverMorphismAlgebra.affineOverMorphismAlgebra_spec k (DualNumber C) B f.val

variable (C' : Type) [CommRing C'] [Algebra k C'] [Algebra B C'] [IsScalarTower k B C']
    (q : C →ₐ[B] C')

theorem affineDualLiftSpaceEquiv_coefficient_map (v : Dual.AlgebraLiftCoordinates.DualCoefficientLifts.Space C k B) :
    AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap (q.restrictScalars k)) ≫
        ((DualLiftConormal.affineDualLiftSpaceEquiv k B C).symm v).val =
      ((DualLiftConormal.affineDualLiftSpaceEquiv k B C').symm (Dual.CoefficientLiftNaturality.dualCoefficientLiftMap k B C C' q v)).val := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (Dual.NumberCoefficients.dualNumberAlgMap (q.restrictScalars k)).toRingHom) ≫
      ((DualLiftConormal.affineDualLiftSpaceEquiv k B C).symm v).val.left =
    ((DualLiftConormal.affineDualLiftSpaceEquiv k B C').symm (Dual.CoefficientLiftNaturality.dualCoefficientLiftMap k B C C' q v)).val.left
  rw [← affineDualLiftSpaceEquiv_symm_spec, ← affineDualLiftSpaceEquiv_symm_spec, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun b => (Dual.CoefficientLiftNaturality.dualCoefficientLiftMap_hom k B C C' q v b).symm)

end

/-! The actual affine scheme lift of a derivation commutes with
the prescribed coefficient map and its induced map of derivations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k B C C' : Type) [CommRing k] [CommRing B] [CommRing C] [CommRing C']
    [Algebra k B] [Algebra k C] [Algebra k C'] [Algebra B C] [Algebra B C']
    [IsScalarTower k B C] [IsScalarTower k B C'] (q : C →ₐ[B] C')

theorem affineDualLiftDerivationEquiv_coefficient_map (d : Derivation k B C) :
    AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap (q.restrictScalars k)) ≫
        ((DualLiftConormal.affineDualLiftDerivationEquiv k B C).symm d).val =
      ((DualLiftConormal.affineDualLiftDerivationEquiv k B C').symm (Dual.CoefficientLiftNaturality.coefficientDerivationMap k B C C' q d)).val := by
  let v := (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C k B).symm d
  have hv : Dual.CoefficientLiftNaturality.dualCoefficientLiftMap k B C C' q v =
      (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C' k B).symm (Dual.CoefficientLiftNaturality.coefficientDerivationMap k B C C' q d) := by
    change (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C' k B).symm
      (Dual.CoefficientLiftNaturality.coefficientDerivationMap k B C C' q (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C k B v)) = _
    rw [LinearEquiv.apply_symm_apply]
  have hc := affineDualLiftSpaceEquiv_coefficient_map k B C C' q v
  rw [hv] at hc
  exact hc

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualDerivationCoefficientMaps

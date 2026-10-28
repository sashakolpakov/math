import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupCoefficientConormal

/-! # Conormal Lift Inverse Formulas -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConormalLiftInverseFormulas

noncomputable section

/-! Inverting conormal coordinates gives the actual affine lift,
followed by inclusion and translation by the reference map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k B C : Type) [CommRing k] [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] [Algebra B C] [IsScalarTower k B C]
    [Algebra B k] [IsScalarTower k B k] [IsScalarTower B k C] [Algebra.FormallySmooth k B]

theorem affineDualLiftConormalEquiv_symm_derivation (d : Derivation k B C) :
    (Affine.DualLiftConormal.affineDualLiftConormalEquiv k B C).symm (PELModuli.IntegralModel.Section.ConormalDerivations.SectionConormal.derivationConormalEquiv k B C d) =
      (Affine.DualLiftConormal.affineDualLiftDerivationEquiv k B C).symm d := by
  change (Affine.DualLiftConormal.affineDualLiftSpaceEquiv k B C).symm
      ((Dual.AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C k B).symm
        ((PELModuli.IntegralModel.Section.ConormalDerivations.SectionConormal.derivationConormalEquiv k B C).symm
          (PELModuli.IntegralModel.Section.ConormalDerivations.SectionConormal.derivationConormalEquiv k B C d))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

variable {A : Over (Spec (.of k))} [GrpObj A]
    (i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ A) [IsOpenImmersion i.left]
    (hi : Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B k (IsScalarTower.toAlgHom k B k) ≫ i = 1)
    (c : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A)

theorem groupCoefficientConormalEquiv_symm_val (q : (RingHom.ker (algebraMap B k)).Cotangent →ₗ[k] C) :
    ((GroupCoefficientConormal.groupCoefficientConormalEquiv k B C i hi c).symm q).val =
      (((Affine.DualLiftConormal.affineDualLiftConormalEquiv k B C).symm q).val ≫ i) * c := rfl

theorem groupCoefficientConormalEquiv_symm_derivation (d : Derivation k B C) :
    ((GroupCoefficientConormal.groupCoefficientConormalEquiv k B C i hi c).symm
      (PELModuli.IntegralModel.Section.ConormalDerivations.SectionConormal.derivationConormalEquiv k B C d)).val =
      (((Affine.DualLiftConormal.affineDualLiftDerivationEquiv k B C).symm d).val ≫ i) * c := by
  rw [groupCoefficientConormalEquiv_symm_val, affineDualLiftConormalEquiv_symm_derivation]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConormalLiftInverseFormulas

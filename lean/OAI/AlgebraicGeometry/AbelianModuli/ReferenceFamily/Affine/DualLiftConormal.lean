import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftReduction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AlgebraLiftCoordinates

/-! # Dual Lift Conormal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftConormal

noncomputable section

/-! Actual affine scheme lifts over arbitrary coefficient algebras
identify with derivations and, at a smooth section, the dual of its
conormal. The comparisons retain the coefficients of the actual map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k B C : Type) [CommRing k] [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] [Algebra B C] [IsScalarTower k B C]

def affineDualLiftSpaceEquiv :
    {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C)} ≃
      Dual.AlgebraLiftCoordinates.DualCoefficientLifts.Space C k B :=
  (DualLiftReduction.affineDualLiftAlgebraEquiv k B C (IsScalarTower.toAlgHom k B C)).trans (Dual.AlgebraLiftCoordinates.dualAlgebraLiftEquiv k B C)

theorem affineDualLiftSpaceEquiv_hom
    (f : {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C)})
    (b : B) : (affineDualLiftSpaceEquiv k B C f).val.hom b =
      OverMorphismAlgebra.affineOverMorphismAlgebra k (DualNumber C) B f.val b := rfl

def affineDualLiftDerivationEquiv :
    {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C)} ≃
      Derivation k B C :=
  (affineDualLiftSpaceEquiv k B C).trans (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C k B).toEquiv

theorem affineDualLiftDerivationEquiv_apply
    (f : {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C)})
    (b : B) : affineDualLiftDerivationEquiv k B C f b =
      (OverMorphismAlgebra.affineOverMorphismAlgebra k (DualNumber C) B f.val b).snd :=
  Dual.AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv_apply C k B (affineDualLiftSpaceEquiv k B C f) b

variable [Algebra B k] [IsScalarTower k B k] [IsScalarTower B k C] [Algebra.FormallySmooth k B]

def affineDualLiftConormalEquiv :
    {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C)} ≃
      ((RingHom.ker (algebraMap B k)).Cotangent →ₗ[k] C) :=
  (affineDualLiftSpaceEquiv k B C).trans (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.conormalEquiv C k B).toEquiv

theorem affineDualLiftConormalEquiv_toCotangent
    (f : {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C)})
    (b : RingHom.ker (algebraMap B k)) :
    affineDualLiftConormalEquiv k B C f (Ideal.toCotangent _ b) =
      (OverMorphismAlgebra.affineOverMorphismAlgebra k (DualNumber C) B f.val b).snd :=
  Dual.AlgebraLiftCoordinates.DualCoefficientLifts.conormalEquiv_toCotangent C k B (affineDualLiftSpaceEquiv k B C f) b

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftConormal

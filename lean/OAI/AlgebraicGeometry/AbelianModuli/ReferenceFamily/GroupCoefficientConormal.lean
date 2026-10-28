import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftConormal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupLiftOpenCoordinates

/-! # Group Coefficient Conormal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupCoefficientConormal

noncomputable section

/-! An actual affine neighborhood of the group identity gives
conormal coordinates for lifts with arbitrary coefficient algebras.
The coordinates recover the original map after its actual translation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k B C : Type) [CommRing k] [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] [Algebra B C] [IsScalarTower k B C]
    [Algebra B k] [IsScalarTower k B k] [IsScalarTower B k C]
    {A : Over (Spec (.of k))} [GrpObj A]
    (i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ A) [IsOpenImmersion i.left]
    (hi : Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B k (IsScalarTower.toAlgHom k B k) ≫ i = 1)

omit [IsOpenImmersion i.left] in
include hi in
theorem affineGroupIdentity_coefficients :
    Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C) ≫ i = 1 := by
  have h : (Algebra.ofId k C).comp (IsScalarTower.toAlgHom k B k) =
      IsScalarTower.toAlgHom k B C := by
    apply AlgHom.ext
    intro b
    exact (IsScalarTower.algebraMap_apply B k C b).symm
  have hc := Affine.OverMorphismAlgebra.affineOverAlgHom_comp k C k (Algebra.ofId k C) (IsScalarTower.toAlgHom k B k)
  rw [h] at hc
  rw [← hc, Category.assoc, hi, MonObj.comp_one]

def groupCoefficientOpenLiftEquiv (c : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A) :
    {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c} ≃
      {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B //
        Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C)} :=
  GroupLiftOpenCoordinates.groupLiftOpenEquiv (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C) i
    (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C))
    (affineGroupIdentity_coefficients k B C i hi) c

def groupCoefficientDerivationEquiv (c : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A) :
    {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c} ≃
      Derivation k B C :=
  (groupCoefficientOpenLiftEquiv k B C i hi c).trans (Affine.DualLiftConormal.affineDualLiftDerivationEquiv k B C)

def groupCoefficientConormalEquiv [Algebra.FormallySmooth k B] (c : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A) :
    {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c} ≃
      ((RingHom.ker (algebraMap B k)).Cotangent →ₗ[k] C) :=
  (groupCoefficientOpenLiftEquiv k B C i hi c).trans (Affine.DualLiftConormal.affineDualLiftConormalEquiv k B C)

theorem groupCoefficientOpenLift_recovery (c : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A)
    (f : {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c}) :
    ((groupCoefficientOpenLiftEquiv k B C i hi c f).val ≫ i) * c = f.val :=
  GroupLiftOpenCoordinates.groupLiftOpenEquiv_recovery (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C) i
    (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C))
    (affineGroupIdentity_coefficients k B C i hi) c f

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupCoefficientConormal

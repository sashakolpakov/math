import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.IntrinsicCoefficientPoint

/-! # Chart Coefficient Conormal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartCoefficientConormal

noncomputable section

/-! The affine-open comparison works with arbitrary coefficient
algebras, including localizations at primes. The coefficient point may
be any point of the original affine chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k : Type) [Field k] (B C : Type) [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] [Algebra B C] [IsScalarTower k B C]
    (A : Over (Spec (.of k))) (i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ A) [IsOpenImmersion i.left]

def affineChartCoefficientPoint : EtaleSplittingAt.EtaleSplitting.affineOver k C ⟶ A :=
  AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C) ≫ i

def affineChartCoefficientLiftDerivationEquiv :
    {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = affineChartCoefficientPoint k B C A i} ≃
      Derivation k B C :=
  (Open.ImmersionLiftFibers.openImmersionLiftFiberEquiv (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C) i
    (AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C))).symm.trans (DualLiftConormal.affineDualLiftDerivationEquiv k B C)

variable [GrpObj A] [Smooth A.hom]

def affineChartCoefficientConormalEquiv : Derivation k B C ≃ (Constructed.IdentityConormal.constructedIdentityConormal k A →ₗ[k] C) :=
  (affineChartCoefficientLiftDerivationEquiv k B C A i).symm.trans
    ((Equiv.subtypeEquivRight (fun f =>
      show (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = affineChartCoefficientPoint k B C A i) ↔
        (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫
          IntrinsicCoefficientPoint.openAffineLiftReference k C A (affineChartCoefficientPoint k B C A i)) by
            rw [IntrinsicCoefficientPoint.openAffineLiftReference_reduction])).trans
      (Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv k A C
        (IntrinsicCoefficientPoint.openAffineLiftReference k C A (affineChartCoefficientPoint k B C A i))))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartCoefficientConormal

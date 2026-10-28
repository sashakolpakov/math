import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartCoefficientConormal

/-! # Chart Lift Inclusion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartLiftInclusion

noncomputable section

/-! Composing an original affine lift with its open inclusion retains
the same coefficient derivation in the constructed chart comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k : Type) [Field k] (B C : Type) [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] [Algebra B C] [IsScalarTower k B C]
    (A : Over (Spec (.of k))) (i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ A) [IsOpenImmersion i.left]

def affineChartCoefficientLiftInclusion
    (u : {u : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ u = AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C)}) :
    {u : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ u = ChartCoefficientConormal.affineChartCoefficientPoint k B C A i} :=
  (Open.ImmersionLiftFibers.openImmersionLiftFiberEquiv (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C) i
    (AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C))) u

theorem affineChartCoefficientLiftInclusion_value
    (u : {u : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ u = AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C)}) :
    (affineChartCoefficientLiftInclusion k B C A i u).val = u.val ≫ i := rfl

theorem affineChartCoefficientLiftInclusion_derivation
    (u : {u : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ u = AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C)}) :
    ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv k B C A i (affineChartCoefficientLiftInclusion k B C A i u) =
      DualLiftConormal.affineDualLiftDerivationEquiv k B C u := by
  let E := Open.ImmersionLiftFibers.openImmersionLiftFiberEquiv (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C) i
    (AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C))
  exact congrArg (DualLiftConormal.affineDualLiftDerivationEquiv k B C) (E.symm_apply_apply u)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartLiftInclusion

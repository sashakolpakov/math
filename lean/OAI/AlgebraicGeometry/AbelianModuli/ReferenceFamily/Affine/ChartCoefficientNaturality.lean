import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualDerivationCoefficientMaps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartCoefficientConormal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientMapSquares

/-! # Chart Coefficient Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartCoefficientNaturality

noncomputable section

/-! Actual affine-chart coefficient points, their constant references,
and their derivation lifts commute with coefficient changes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k : Type) [Field k] (B C C' : Type) [CommRing B] [CommRing C] [CommRing C']
    [Algebra k B] [Algebra k C] [Algebra k C'] [Algebra B C] [Algebra B C']
    [IsScalarTower k B C] [IsScalarTower k B C'] (q : C →ₐ[B] C')
    (A : Over (Spec (.of k))) (i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ A)

theorem affineChartCoefficientPoint_natural :
    AlgebraAutomorphismNaturality.affineOverAlgHom k C C' (q.restrictScalars k) ≫ ChartCoefficientConormal.affineChartCoefficientPoint k B C A i =
      ChartCoefficientConormal.affineChartCoefficientPoint k B C' A i := by
  change AlgebraAutomorphismNaturality.affineOverAlgHom k C C' (q.restrictScalars k) ≫
      (AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C) ≫ i) =
    AlgebraAutomorphismNaturality.affineOverAlgHom k B C' (IsScalarTower.toAlgHom k B C') ≫ i
  rw [← Category.assoc, OverMorphismAlgebra.affineOverAlgHom_comp]
  apply congrArg (fun f => f ≫ i)
  apply congrArg (AlgebraAutomorphismNaturality.affineOverAlgHom k B C')
  exact AlgHom.ext (fun b => q.commutes b)

theorem affineChartCoefficientReference_natural :
    AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap (q.restrictScalars k)) ≫
        IntrinsicCoefficientPoint.openAffineLiftReference k C A (ChartCoefficientConormal.affineChartCoefficientPoint k B C A i) =
      IntrinsicCoefficientPoint.openAffineLiftReference k C' A (ChartCoefficientConormal.affineChartCoefficientPoint k B C' A i) := by
  change AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap (q.restrictScalars k)) ≫
      (Dual.CoefficientSchemeTests.dualCoefficientProjection k C ≫ ChartCoefficientConormal.affineChartCoefficientPoint k B C A i) =
    Dual.CoefficientSchemeTests.dualCoefficientProjection k C' ≫ ChartCoefficientConormal.affineChartCoefficientPoint k B C' A i
  rw [← Category.assoc, Dual.CoefficientMapSquares.dualCoefficientProjection_natural, Category.assoc, affineChartCoefficientPoint_natural]

variable [IsOpenImmersion i.left]

theorem affineChartCoefficientLiftDerivationEquiv_natural (d : Derivation k B C) :
    AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap (q.restrictScalars k)) ≫
        ((ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv k B C A i).symm d).val =
      ((ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv k B C' A i).symm (Dual.CoefficientLiftNaturality.coefficientDerivationMap k B C C' q d)).val := by
  change AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap (q.restrictScalars k)) ≫
      (((DualLiftConormal.affineDualLiftDerivationEquiv k B C).symm d).val ≫ i) =
    ((DualLiftConormal.affineDualLiftDerivationEquiv k B C').symm (Dual.CoefficientLiftNaturality.coefficientDerivationMap k B C C' q d)).val ≫ i
  rw [← Category.assoc, DualDerivationCoefficientMaps.affineDualLiftDerivationEquiv_coefficient_map]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartCoefficientNaturality

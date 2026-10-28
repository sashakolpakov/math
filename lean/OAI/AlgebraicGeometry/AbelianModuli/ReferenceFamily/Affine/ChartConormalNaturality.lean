import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartCoefficientNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalCoefficientSquare

/-! # Chart Conormal Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartConormalNaturality

noncomputable section

/-! The actual affine-chart derivation-to-conormal comparison commutes
with coefficient homomorphisms, including evaluation at complex points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k : Type) [Field k] (B C C' : Type) [CommRing B] [CommRing C] [CommRing C']
    [Algebra k B] [Algebra k C] [Algebra k C'] [Algebra B C] [Algebra B C']
    [IsScalarTower k B C] [IsScalarTower k B C'] (q : C →ₐ[B] C')
    (A : Over (Spec (.of k))) [GrpObj A] [Smooth A.hom]
    (i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ A) [IsOpenImmersion i.left]

theorem affineChartCoefficientConormalEquiv_natural (d : Derivation k B C) (z : Constructed.IdentityConormal.constructedIdentityConormal k A) :
    ChartCoefficientConormal.affineChartCoefficientConormalEquiv k B C' A i (Dual.CoefficientLiftNaturality.coefficientDerivationMap k B C C' q d) z =
      q (ChartCoefficientConormal.affineChartCoefficientConormalEquiv k B C A i d z) := by
  let c := IntrinsicCoefficientPoint.openAffineLiftReference k C A (ChartCoefficientConormal.affineChartCoefficientPoint k B C A i)
  let c' := IntrinsicCoefficientPoint.openAffineLiftReference k C' A (ChartCoefficientConormal.affineChartCoefficientPoint k B C' A i)
  let f := (ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv k B C A i).symm d
  let f' := (ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv k B C' A i).symm (Dual.CoefficientLiftNaturality.coefficientDerivationMap k B C C' q d)
  have hr : Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f.val = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c :=
    f.property.trans (IntrinsicCoefficientPoint.openAffineLiftReference_reduction k C A (ChartCoefficientConormal.affineChartCoefficientPoint k B C A i)).symm
  have hr' : Dual.CoefficientSchemeTests.dualCoefficientOrigin k C' ≫ f'.val = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C' ≫ c' :=
    f'.property.trans (IntrinsicCoefficientPoint.openAffineLiftReference_reduction k C' A (ChartCoefficientConormal.affineChartCoefficientPoint k B C' A i)).symm
  exact Constructed.ConormalCoefficientSquare.constructedIdentityLiftConormalEquiv_square k A C C' (q.restrictScalars k) c c' ⟨f.val, hr⟩ ⟨f'.val, hr'⟩
    (ChartCoefficientNaturality.affineChartCoefficientReference_natural k B C C' q A i)
    (ChartCoefficientNaturality.affineChartCoefficientLiftDerivationEquiv_natural k B C C' q A i d) z

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartConormalNaturality

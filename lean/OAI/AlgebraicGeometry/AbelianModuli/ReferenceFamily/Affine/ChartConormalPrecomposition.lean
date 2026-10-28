import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftPrecomposition
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartCoefficientConormal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalCongruence

/-! # Chart Conormal Precomposition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartConormalPrecomposition

noncomputable section

/-! The constructed conormal comparison is independent of restriction
from one actual affine chart to a smaller affine chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k : Type) [Field k] (B D C : Type) [CommRing B] [CommRing D] [CommRing C]
    [Algebra k B] [Algebra k D] [Algebra k C] [Algebra B D] [Algebra B C] [Algebra D C]
    [IsScalarTower k B D] [IsScalarTower k B C] [IsScalarTower k D C] [IsScalarTower B D C]
    (A : Over (Spec (.of k))) (iB : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ A) (iD : EtaleSplittingAt.EtaleSplitting.affineOver k D ⟶ A)
    (hi : AlgebraAutomorphismNaturality.affineOverAlgHom k B D (IsScalarTower.toAlgHom k B D) ≫ iB = iD)

include hi in
theorem affineChartCoefficientPoint_precomposition :
    ChartCoefficientConormal.affineChartCoefficientPoint k B C A iB = ChartCoefficientConormal.affineChartCoefficientPoint k D C A iD := by
  change AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C) ≫ iB =
    AlgebraAutomorphismNaturality.affineOverAlgHom k D C (IsScalarTower.toAlgHom k D C) ≫ iD
  rw [← DualLiftPrecomposition.affineCoefficientPoint_precomposition k B D C, Category.assoc, hi]

variable [IsOpenImmersion iB.left] [IsOpenImmersion iD.left]

include hi in
theorem affineChartCoefficientLiftDerivationEquiv_precomposition (d : Derivation k D C) :
    ((ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv k B C A iB).symm
      (Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k B D C d)).val =
    ((ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv k D C A iD).symm d).val := by
  change ((DualLiftConormal.affineDualLiftDerivationEquiv k B C).symm
      (Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k B D C d)).val ≫ iB =
    ((DualLiftConormal.affineDualLiftDerivationEquiv k D C).symm d).val ≫ iD
  rw [← DualLiftPrecomposition.affineDualLiftDerivationEquiv_precomposition k B D C d, Category.assoc, hi]

variable [GrpObj A] [Smooth A.hom]

include hi in
theorem affineChartCoefficientConormalEquiv_precomposition (d : Derivation k D C) :
    ChartCoefficientConormal.affineChartCoefficientConormalEquiv k B C A iB (Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k B D C d) =
      ChartCoefficientConormal.affineChartCoefficientConormalEquiv k D C A iD d := by
  let c := IntrinsicCoefficientPoint.openAffineLiftReference k C A (ChartCoefficientConormal.affineChartCoefficientPoint k B C A iB)
  let c' := IntrinsicCoefficientPoint.openAffineLiftReference k C A (ChartCoefficientConormal.affineChartCoefficientPoint k D C A iD)
  let f := (ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv k B C A iB).symm
    (Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k B D C d)
  let f' := (ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv k D C A iD).symm d
  have hr : Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f.val = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c :=
    f.property.trans (IntrinsicCoefficientPoint.openAffineLiftReference_reduction k C A (ChartCoefficientConormal.affineChartCoefficientPoint k B C A iB)).symm
  have hr' : Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f'.val = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c' :=
    f'.property.trans (IntrinsicCoefficientPoint.openAffineLiftReference_reduction k C A (ChartCoefficientConormal.affineChartCoefficientPoint k D C A iD)).symm
  have hc : c = c' := congrArg (IntrinsicCoefficientPoint.openAffineLiftReference k C A)
    (affineChartCoefficientPoint_precomposition k B D C A iB iD hi)
  exact Constructed.ConormalCongruence.constructedIdentityLiftConormalEquiv_congr k A C c c' ⟨f.val, hr⟩ ⟨f'.val, hr'⟩ hc
    (affineChartCoefficientLiftDerivationEquiv_precomposition k B D C A iB iD hi d)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartConormalPrecomposition

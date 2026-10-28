import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartCoefficientConormal

/-! # Conormal Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConormalLift

noncomputable section

/-! Affine conormal coordinates of the derivation of an original
lift are its original group-lift coordinates relative to the constant lift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k : Type) [Field k] (B C : Type) [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] [Algebra B C] [IsScalarTower k B C]
    (A : Over (Spec (.of k))) [GrpObj A] [Smooth A.hom]
    (i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ A) [IsOpenImmersion i.left]

theorem affineChartConormal_originalLift
    (u : {u : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ u = ChartCoefficientConormal.affineChartCoefficientPoint k B C A i}) :
    ChartCoefficientConormal.affineChartCoefficientConormalEquiv k B C A i
        (ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv k B C A i u) =
      Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv k A C
        (IntrinsicCoefficientPoint.openAffineLiftReference k C A (ChartCoefficientConormal.affineChartCoefficientPoint k B C A i))
        ⟨u.val, u.property.trans (IntrinsicCoefficientPoint.openAffineLiftReference_reduction k C A
          (ChartCoefficientConormal.affineChartCoefficientPoint k B C A i)).symm⟩ := by
  let E := ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv k B C A i
  let r := IntrinsicCoefficientPoint.openAffineLiftReference k C A (ChartCoefficientConormal.affineChartCoefficientPoint k B C A i)
  let Q := fun w : {w : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ w = ChartCoefficientConormal.affineChartCoefficientPoint k B C A i} =>
    Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv k A C r
      ⟨w.val, w.property.trans (IntrinsicCoefficientPoint.openAffineLiftReference_reduction k C A
        (ChartCoefficientConormal.affineChartCoefficientPoint k B C A i)).symm⟩
  exact congrArg Q (E.symm_apply_apply u)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConormalLift

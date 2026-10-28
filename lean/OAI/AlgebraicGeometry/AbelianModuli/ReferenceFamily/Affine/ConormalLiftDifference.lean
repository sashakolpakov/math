import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConormalLift
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CoefficientConormalLinearity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.ConormalCocycle

/-! # Conormal Lift Difference -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConormalLiftDifference

noncomputable section

/-! The conormal discrepancy of two actual lifts through an affine
chart is the conormal coordinate of the difference of their original
coefficient derivations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (A : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral A.left] [Smooth A.hom] [GrpObj A]
    (B : CommAlgCat ℂ) [IsDomain B] [Algebra.Smooth ℂ B]
    (i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ A) [IsOpenImmersion i.left]
    (C : Type) [CommRing C] [Algebra ℂ C] [Algebra B C] [IsScalarTower ℂ B C]
    [Algebra.FiniteType ℂ C] [IsReduced C]

theorem affineConormalLiftDifference
    (u v : {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber C) ⟶ A //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ u = ChartCoefficientConormal.affineChartCoefficientPoint ℂ B C A i}) :
    Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A C u.val ⟨v.val, v.property.trans u.property.symm⟩ =
      Regular.CoefficientConormalLinearity.regularCoefficientConormalLinearEquiv A B i C
        (ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv ℂ B C A i v -
          ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv ℂ B C A i u) := by
  let r := IntrinsicCoefficientPoint.openAffineLiftReference ℂ C A (ChartCoefficientConormal.affineChartCoefficientPoint ℂ B C A i)
  have hr := IntrinsicCoefficientPoint.openAffineLiftReference_reduction ℂ C A (ChartCoefficientConormal.affineChartCoefficientPoint ℂ B C A i)
  have hu := ConormalLift.affineChartConormal_originalLift ℂ B C A i u
  have hv := ConormalLift.affineChartConormal_originalLift ℂ B C A i v
  have hc := Regular.ConormalCocycle.regularConormalReference_cocycle A C r u.val v.val (u.property.trans hr.symm)
    (v.property.trans u.property.symm)
  have h : Regular.CoefficientConormalLinearity.regularCoefficientConormalLinearEquiv A B i C
        (ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv ℂ B C A i u) +
      Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A C u.val ⟨v.val, v.property.trans u.property.symm⟩ =
        Regular.CoefficientConormalLinearity.regularCoefficientConormalLinearEquiv A B i C
          (ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv ℂ B C A i v) :=
    (congrArg (fun z => z + Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A C u.val
      ⟨v.val, v.property.trans u.property.symm⟩) hu).trans (hc.trans hv.symm)
  exact ((eq_sub_iff_add_eq).mpr ((add_comm _ _).trans h)).trans
    ((Regular.CoefficientConormalLinearity.regularCoefficientConormalLinearEquiv A B i C).map_sub _ _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConormalLiftDifference

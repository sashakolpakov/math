import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConormalLiftDifference
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationConormalLinearity

/-! # Presentation Lift Difference -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationLiftDifference

noncomputable section

/-! On any actual affine presentation of an open in the fixed group,
including an empty open, the original lift discrepancy has exactly the
conormal coordinates of its difference derivation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (A : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral A.left] [Smooth A.hom] [GrpObj A]
    (B : CommAlgCat ℂ) (i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ A) [IsOpenImmersion i.left]

theorem affinePresentationLiftDifference
    (u v : {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber B) ⟶ A //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ B ≫ u = ChartCoefficientConormal.affineChartCoefficientPoint ℂ B B A i}) :
    Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A B u.val ⟨v.val, v.property.trans u.property.symm⟩ =
      PresentationConormalLinearity.affinePresentationConormalLinearEquiv A B i
        (ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv ℂ B B A i v -
          ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv ℂ B B A i u) := by
  cases subsingleton_or_nontrivial B with
  | inl h =>
    let := h
    exact Subsingleton.elim _ _
  | inr h =>
    let := h
    have : Algebra.Smooth ℂ B := PresentationConormalLinearity.affinePresentationAlgebra_smooth A B i
    have : IsDomain B := PresentationConormalLinearity.affinePresentationAlgebra_isDomain A B i
    exact ConormalLiftDifference.affineConormalLiftDifference A B i B u v

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationLiftDifference

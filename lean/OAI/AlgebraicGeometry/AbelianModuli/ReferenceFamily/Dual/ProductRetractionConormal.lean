import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductRetractionDifferences
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartLiftInclusion
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationLiftDifference

/-! # Product Retraction Conormal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductRetractionConormal

noncomputable section

/-! The original product-chart transition derivation is exactly the
conormal discrepancy of its actual retractions into the fixed group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (A : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral A.left] [Smooth A.hom] [GrpObj A]
    (B : CommAlgCat ℂ) (i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ A) [IsOpenImmersion i.left]
    (S : Type) [CommRing S] [Algebra (DualNumber ℂ) S]
    (q : S →+* B) (f r : S ≃ₐ[DualNumber ℂ] (DualNumber ℂ ⊗[ℂ] B))
    (hf : ∀ s, TensorReduction.dualTensorReduction ℂ B (f s) = q s)
    (hr : ∀ s, TensorReduction.dualTensorReduction ℂ B (r s) = q s)

def productChartGroupRetraction :
    {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber B) ⟶ A //
      CoefficientSchemeTests.dualCoefficientOrigin ℂ B ≫ u = Affine.ChartCoefficientConormal.affineChartCoefficientPoint ℂ B B A i} :=
  Affine.ChartLiftInclusion.affineChartCoefficientLiftInclusion ℂ B B A i (ProductRetractionDifferences.dualProductRetractionLift ℂ B S q f r hf hr)

omit [IsIntegral A.left] [Smooth A.hom] [GrpObj A] in
theorem productChartGroupRetraction_derivation :
    Affine.ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv ℂ B B A i (productChartGroupRetraction A B i S q f r hf hr) =
      ReferenceFamily.Smooth.DualChartDifferences.dualProductChartDifference q f r hf hr :=
  (Affine.ChartLiftInclusion.affineChartCoefficientLiftInclusion_derivation ℂ B B A i (ProductRetractionDifferences.dualProductRetractionLift ℂ B S q f r hf hr)).trans
    (ProductRetractionDifferences.dualProductRetractionLift_derivation ℂ B S q f r hf hr)

theorem productChartGroupRetraction_conormal
    (g : S ≃ₐ[DualNumber ℂ] (DualNumber ℂ ⊗[ℂ] B))
    (hg : ∀ s, TensorReduction.dualTensorReduction ℂ B (g s) = q s) :
    Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A B (productChartGroupRetraction A B i S q g r hg hr).val
        ⟨(productChartGroupRetraction A B i S q f r hf hr).val,
          (productChartGroupRetraction A B i S q f r hf hr).property.trans
            (productChartGroupRetraction A B i S q g r hg hr).property.symm⟩ =
      Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv A B i (ReferenceFamily.Smooth.DualChartDifferences.dualProductChartDifference q f g hf hg) := by
  let u := productChartGroupRetraction A B i S q f r hf hr
  let v := productChartGroupRetraction A B i S q g r hg hr
  have h := Affine.PresentationLiftDifference.affinePresentationLiftDifference A B i v u
  have hd : Affine.ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv ℂ B B A i u -
      Affine.ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv ℂ B B A i v = ReferenceFamily.Smooth.DualChartDifferences.dualProductChartDifference q f g hf hg := by
    rw [productChartGroupRetraction_derivation, productChartGroupRetraction_derivation]
    exact sub_eq_iff_eq_add.mpr (ReferenceFamily.Smooth.DualChartDifferences.dualProductChartDifference_cocycle q f g r hf hg hr).symm
  exact h.trans (congrArg (Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv A B i) hd)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductRetractionConormal

import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ChartRetractionRestriction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductRetractionConormal

/-! # Chart Group Retraction Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ChartGroupRetractionRestriction

noncomputable section

/-! Original affine product-chart retractions into a fixed scheme
commute with restriction whenever their original product charts and
fixed-fiber affine inclusions commute. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) (A B : CommAlgCat ℂ)
    (i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ A ⟶ G) (j : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G)
    [IsOpenImmersion i.left] [IsOpenImmersion j.left]
    (S T : Type) [CommRing S] [CommRing T]
    [Algebra (DualNumber ℂ) S] [Algebra (DualNumber ℂ) T]
    (m : S →ₐ[DualNumber ℂ] T)
    (f r : S ≃ₐ[DualNumber ℂ] (DualNumber ℂ ⊗[ℂ] A))
    (g s : T ≃ₐ[DualNumber ℂ] (DualNumber ℂ ⊗[ℂ] B))
    (q : A →ₐ[ℂ] B)
    (h : g.toAlgHom.comp m =
      (Algebra.TensorProduct.map (AlgHom.id (DualNumber ℂ) (DualNumber ℂ)) q).comp f.toAlgHom)
    (hi : Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ A B q ≫ i = j)
    (qS : S →+* A) (qT : T →+* B)
    (hf : ∀ x, Dual.TensorReduction.dualTensorReduction ℂ A (f x) = qS x)
    (hr : ∀ x, Dual.TensorReduction.dualTensorReduction ℂ A (r x) = qS x)
    (hg : ∀ x, Dual.TensorReduction.dualTensorReduction ℂ B (g x) = qT x)
    (hs : ∀ x, Dual.TensorReduction.dualTensorReduction ℂ B (s x) = qT x)

include h hi

theorem productChartGroupRetraction_restrict :
    Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber A) (DualNumber B)
        (Dual.TensorMapCoordinates.dualTensorMapCoordinates (ChartMorphismCoordinates.productChartMorphismCoordinates m r s)) ≫
      (Dual.ProductRetractionConormal.productChartGroupRetraction G A i S qS f r hf hr).val =
    (Dual.ProductRetractionConormal.productChartGroupRetraction G B j T qT g s hg hs).val := by
  change Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber A) (DualNumber B)
      (Dual.TensorMapCoordinates.dualTensorMapCoordinates (ChartMorphismCoordinates.productChartMorphismCoordinates m r s)) ≫
      ((Dual.ProductRetractionDifferences.dualProductRetractionLift ℂ A S qS f r hf hr).val ≫ i) =
    (Dual.ProductRetractionDifferences.dualProductRetractionLift ℂ B T qT g s hg hs).val ≫ j
  rw [← Category.assoc, ChartRetractionRestriction.productChartRetraction_scheme_square ℂ A B S T m f r g s q h qS qT hf hr hg hs,
    Category.assoc, hi]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ChartGroupRetractionRestriction

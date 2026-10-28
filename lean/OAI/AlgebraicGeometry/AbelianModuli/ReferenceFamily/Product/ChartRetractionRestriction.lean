import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ChartMorphismCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductRetractionDifferences
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorMapCoordinateLaws

/-! # Chart Retraction Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ChartRetractionRestriction

noncomputable section

section

/-! When selected product charts commute with an original map of
affine families, their retractions commute in arbitrary reference
product coordinates. The square retains the actual coefficient map. -/

open scoped TensorProduct

variable {k A B S T : Type} [CommRing k] [CommRing A] [CommRing B]
    [CommRing S] [CommRing T] [Algebra k A] [Algebra k B]
    [Algebra (DualNumber k) S] [Algebra (DualNumber k) T]
    (m : S →ₐ[DualNumber k] T)
    (f r : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (g s : T ≃ₐ[DualNumber k] (DualNumber k ⊗[k] B))
    (q : A →ₐ[k] B)
    (h : g.toAlgHom.comp m =
      (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q).comp f.toAlgHom)

include h

theorem productChartRetraction_tensor_square :
    (ChartMorphismCoordinates.productChartMorphismCoordinates m r s).comp (Smooth.DualChartDifferences.dualProductChartTransition f r).toAlgHom =
      (Smooth.DualChartDifferences.dualProductChartTransition g s).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q) := by
  apply AlgHom.ext
  intro u
  change s (m (r.symm (r (f.symm u)))) =
    s (g.symm (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q u))
  rw [r.symm_apply_apply]
  apply congrArg s
  apply g.injective
  rw [g.apply_symm_apply]
  have H := AlgHom.congr_fun h (f.symm u)
  change g (m (f.symm u)) =
    Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q (f (f.symm u)) at H
  rw [f.apply_symm_apply] at H
  exact H

theorem productChartRetraction_coefficient_square :
    (Dual.TensorMapCoordinates.dualTensorMapCoordinates (ChartMorphismCoordinates.productChartMorphismCoordinates m r s)).comp
        (Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates (Smooth.DualChartDifferences.dualProductChartTransition f r)).toAlgHom =
      (Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates (Smooth.DualChartDifferences.dualProductChartTransition g s)).toAlgHom.comp (Dual.NumberCoefficients.dualNumberAlgMap q) := by
  have H := congrArg Dual.TensorMapCoordinates.dualTensorMapCoordinates (productChartRetraction_tensor_square m f r g s q h)
  rw [Dual.TensorMapCoordinateLaws.dualTensorMapCoordinates_comp, Dual.TensorMapCoordinateLaws.dualTensorMapCoordinates_comp,
    Dual.TensorMapCoordinateLaws.dualTensorMapCoordinates_equiv, Dual.TensorMapCoordinateLaws.dualTensorMapCoordinates_equiv, Dual.TensorMapCoordinateLaws.dualTensorMapCoordinates_coefficient] at H
  exact H

end

/-! The algebra restriction square for the original product-chart
retractions is exactly a square of their actual affine-scheme lifts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k A B S T : Type) [CommRing k] [CommRing A] [CommRing B]
    [CommRing S] [CommRing T] [Algebra k A] [Algebra k B]
    [Algebra (DualNumber k) S] [Algebra (DualNumber k) T]
    (m : S →ₐ[DualNumber k] T)
    (f r : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (g s : T ≃ₐ[DualNumber k] (DualNumber k ⊗[k] B))
    (q : A →ₐ[k] B)
    (h : g.toAlgHom.comp m =
      (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q).comp f.toAlgHom)
    (qS : S →+* A) (qT : T →+* B)
    (hf : ∀ x, Dual.TensorReduction.dualTensorReduction k A (f x) = qS x)
    (hr : ∀ x, Dual.TensorReduction.dualTensorReduction k A (r x) = qS x)
    (hg : ∀ x, Dual.TensorReduction.dualTensorReduction k B (g x) = qT x)
    (hs : ∀ x, Dual.TensorReduction.dualTensorReduction k B (s x) = qT x)

include h

theorem productChartRetraction_scheme_square :
    Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber A) (DualNumber B)
        (Dual.TensorMapCoordinates.dualTensorMapCoordinates (ChartMorphismCoordinates.productChartMorphismCoordinates m r s)) ≫
      (Dual.ProductRetractionDifferences.dualProductRetractionLift k A S qS f r hf hr).val =
    (Dual.ProductRetractionDifferences.dualProductRetractionLift k B T qT g s hg hs).val ≫ Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k A B q := by
  change Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber A) (DualNumber B)
      (Dual.TensorMapCoordinates.dualTensorMapCoordinates (ChartMorphismCoordinates.productChartMorphismCoordinates m r s)) ≫
      Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k A (DualNumber A)
        ((Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates (Smooth.DualChartDifferences.dualProductChartTransition f r)).toAlgHom.comp
          (TrivSqZeroExt.inlAlgHom k A A)) =
    Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B (DualNumber B)
        ((Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates (Smooth.DualChartDifferences.dualProductChartTransition g s)).toAlgHom.comp
          (TrivSqZeroExt.inlAlgHom k B B)) ≫ Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k A B q
  rw [Affine.OverMorphismAlgebra.affineOverAlgHom_comp, Affine.OverMorphismAlgebra.affineOverAlgHom_comp]
  apply congrArg (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k A (DualNumber B))
  apply AlgHom.ext
  intro a
  have H := AlgHom.congr_fun (productChartRetraction_coefficient_square m f r g s q h) (TrivSqZeroExt.inl a)
  have hq : Dual.NumberCoefficients.dualNumberAlgMap q (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (q a) := by
    apply TrivSqZeroExt.ext
    · rfl
    · exact map_zero q
  exact H.trans (congrArg (Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates (Smooth.DualChartDifferences.dualProductChartTransition g s)) hq)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ChartRetractionRestriction

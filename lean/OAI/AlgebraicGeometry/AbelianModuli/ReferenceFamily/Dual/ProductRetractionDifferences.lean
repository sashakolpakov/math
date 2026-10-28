import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TransitionAffineLift
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualChartDifferences

/-! # Product Retraction Differences -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductRetractionDifferences

noncomputable section

/-! Expressing original product-chart retractions in any one product
coordinate chart recovers the original transition derivation as the
difference of their actual affine lift derivations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k B S : Type) [CommRing k] [CommRing B] [CommRing S]
    [Algebra k B] [Algebra (DualNumber k) S]
    (q : S →+* B) (f r : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] B))
    (hf : ∀ s, TensorReduction.dualTensorReduction k B (f s) = q s)
    (hr : ∀ s, TensorReduction.dualTensorReduction k B (r s) = q s)

def dualProductRetractionLift :
    {u : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber B) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B //
      CoefficientSchemeTests.dualCoefficientOrigin k B ≫ u = Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B B (IsScalarTower.toAlgHom k B B)} :=
  TransitionAffineLift.dualTransitionAffineLift k B (Smooth.DualChartDifferences.dualProductChartTransition f r) (Smooth.DualChartDifferences.dualProductChartTransition_reduction q f r hf hr)

theorem dualProductRetractionLift_derivation :
    Affine.DualLiftConormal.affineDualLiftDerivationEquiv k B B (dualProductRetractionLift k B S q f r hf hr) =
      Smooth.DualChartDifferences.dualProductChartDifference q f r hf hr :=
  TransitionAffineLift.dualTransitionAffineLift_derivation k B (Smooth.DualChartDifferences.dualProductChartTransition f r) (Smooth.DualChartDifferences.dualProductChartTransition_reduction q f r hf hr)

theorem dualProductRetractionLift_difference
    (g : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] B))
    (hg : ∀ s, TensorReduction.dualTensorReduction k B (g s) = q s) :
    Affine.DualLiftConormal.affineDualLiftDerivationEquiv k B B (dualProductRetractionLift k B S q f r hf hr) -
        Affine.DualLiftConormal.affineDualLiftDerivationEquiv k B B (dualProductRetractionLift k B S q g r hg hr) =
      Smooth.DualChartDifferences.dualProductChartDifference q f g hf hg := by
  rw [dualProductRetractionLift_derivation, dualProductRetractionLift_derivation]
  exact sub_eq_iff_eq_add.mpr (Smooth.DualChartDifferences.dualProductChartDifference_cocycle q f g r hf hg hr).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductRetractionDifferences

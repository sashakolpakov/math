import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CorrectedProducts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.Primitives

/-! # Corrected Product Agreement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CorrectedProductAgreement

noncomputable section

/-! A primitive of the native tangent cocycle makes the actual
corrected product charts equal on every common affine subopen. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsSeparated X.hom]
    (U : X.left.AffineOpenCover) (d : Derivation ℂ R ℂ)
    (a : FamilyTangent.Primitives.fixedFamilyDerivationGauges R X U) (ha : FamilyTangent.Primitives.IsFamilyTangentDerivationPrimitive R X U d a)

attribute [local implicit_reducible] AffineCoverIntersections.familyCoverAffineOpen AffineCoverIntersections.familyCoverPairAffineOpen
attribute [local irreducible] CommonOpenProducts.familyCommonOpenProductEquiv

include ha in
theorem familyTangentPrimitive_common (V : X.left.affineOpens) (i j : U.I₀)
    (hi : V.1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U i).1)
    (hj : V.1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U j).1) :
    CommonOpenTangentDifferences.familyCommonOpenTangentDifference ℂ R X hi hj d =
      FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R ℂ X hi (a i) - FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R ℂ X hj (a j) := by
  let t : V.1 ≤ (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 := le_inf hi hj
  have ht := congrArg (FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R ℂ X t) (ha i j)
  rw [map_sub] at ht
  have hl := LinearMap.congr_fun (FamilyTangent.DifferenceNaturality.familyCommonOpenTangentDifference_restrict ℂ R X t
    (show (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U i).1 from inf_le_left)
    (show (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U j).1 from inf_le_right)) d
  have hi' := LinearMap.congr_fun (FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction_comp R ℂ X t
    (show (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U i).1 from inf_le_left)) (a i)
  have hj' := LinearMap.congr_fun (FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction_comp R ℂ X t
    (show (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U j).1 from inf_le_right)) (a j)
  exact hl.symm.trans (ht.trans (congrArg₂ (fun x y => x - y) hi' hj'))

include ha in
theorem familyCorrectedProductEquiv_common_eq (V : X.left.affineOpens) (i j : U.I₀)
    (hi : V.1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U i).1)
    (hj : V.1 ≤ (AffineCoverIntersections.familyCoverAffineOpen R X U j).1) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra ℂ R d
    letI : Module R (DualNumber ℂ) := qD.toModule
    letI : SMul R (DualNumber ℂ) := qD.toSMul
    CorrectedProducts.familyCorrectedProductEquiv ℂ R X hi d (a i) = CorrectedProducts.familyCorrectedProductEquiv ℂ R X hj d (a j) := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra ℂ R d
  let : Module R (DualNumber ℂ) := qD.toModule
  let : SMul R (DualNumber ℂ) := qD.toSMul
  apply ReferenceFamily.Smooth.DualChartGauges.gaugeDualProductChart_eq_of_coboundary (k := ℂ)
    (A := ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X V) (S := DualNumber ℂ ⊗[R] AffineTangentLifts.familyAffineRing R X V)
    (BaseTangentTensor.baseTangentScalarReduction ℂ R (AffineTangentLifts.familyAffineRing R X V) d)
    (CommonOpenProducts.familyCommonOpenProductEquiv ℂ R X hi d) (CommonOpenProducts.familyCommonOpenProductEquiv ℂ R X hj d)
    (CommonOpenProducts.familyCommonOpenProductEquiv_reduction ℂ R X hi d) (CommonOpenProducts.familyCommonOpenProductEquiv_reduction ℂ R X hj d)
  exact (CommonOpenProducts.familyCommonOpenProduct_transition ℂ R X hi hj d).trans
    (familyTangentPrimitive_common R X U d a ha V i j hi hj)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CorrectedProductAgreement

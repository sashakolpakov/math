import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenTangentDifferences
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentDerivationProduct
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.TransitionLinearComparison

/-! # Common Open Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenProducts

noncomputable section

/-! Restricted affine-family tangent lifts construct actual product
charts on common opens. Their transition derivations are exactly the
previously constructed linear fixed-fiber differences. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R))) [Smooth X.hom]

attribute [local instance 50] AffineTangentLifts.familyAffineCoefficientAlgebra
attribute [local instance] AffineTangentLifts.familyAffineCoefficientTower Algebra.TensorProduct.rightAlgebra
attribute [local instance] PointFiberTensorLifts.pointFiberTensor_scalarTower

def familyCommonOpenProductEquiv {V W : X.left.affineOpens} (h : V.1 ≤ W.1) (d : Derivation k R k) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    (DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X V) ≃ₐ[DualNumber k]
      (DualNumber k ⊗[k] (k ⊗[R] AffineTangentLifts.familyAffineRing R X V)) := by
  have : Algebra.Smooth R (AffineTangentLifts.familyAffineRing R X V) := Affine.OpenDiagram.familyAffineCoordinate_smooth R X V
  exact TangentDerivationProduct.tangentDerivationProductEquiv k R (AffineTangentLifts.familyAffineRing R X V) d
    (CommonOpenTangentDifferences.familyRestrictedTangent k R X h d) (CommonOpenTangentDifferences.familyRestrictedTangent_base k R X h d)

theorem familyCommonOpenProductEquiv_snd {V W : X.left.affineOpens}
    (h : V.1 ≤ W.1) (d : Derivation k R k) (a : AffineTangentLifts.familyAffineRing R X V) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    (Dual.NumberCoefficients.dualTensorCoefficientEquiv k (k ⊗[R] AffineTangentLifts.familyAffineRing R X V)
      (familyCommonOpenProductEquiv k R X h d ((1 : DualNumber k) ⊗ₜ[R] a))).snd =
        CommonOpenTangentDifferences.familyRestrictedTangent k R X h d a := by
  have : Algebra.Smooth R (AffineTangentLifts.familyAffineRing R X V) := Affine.OpenDiagram.familyAffineCoordinate_smooth R X V
  exact TangentDerivationProduct.tangentDerivationProductEquiv_snd k R (AffineTangentLifts.familyAffineRing R X V) d
    (CommonOpenTangentDifferences.familyRestrictedTangent k R X h d) (CommonOpenTangentDifferences.familyRestrictedTangent_base k R X h d) a

theorem familyCommonOpenProductEquiv_reduction {V W : X.left.affineOpens}
    (h : V.1 ≤ W.1) (d : Derivation k R k) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    ∀ p, Dual.TensorReduction.dualTensorReduction k (k ⊗[R] AffineTangentLifts.familyAffineRing R X V)
      (familyCommonOpenProductEquiv k R X h d p) = BaseTangentTensor.baseTangentScalarReduction k R (AffineTangentLifts.familyAffineRing R X V) d p := by
  have : Algebra.Smooth R (AffineTangentLifts.familyAffineRing R X V) := Affine.OpenDiagram.familyAffineCoordinate_smooth R X V
  exact TangentDerivationProduct.tangentDerivationProductEquiv_reduction k R (AffineTangentLifts.familyAffineRing R X V) d
    (CommonOpenTangentDifferences.familyRestrictedTangent k R X h d) (CommonOpenTangentDifferences.familyRestrictedTangent_base k R X h d)

attribute [local irreducible] familyCommonOpenProductEquiv

theorem familyCommonOpenProduct_transition {V W Z : X.left.affineOpens}
    (h : V.1 ≤ W.1) (j : V.1 ≤ Z.1) (d : Derivation k R k) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    ReferenceFamily.Smooth.DualChartDifferences.dualProductChartDifference (k := k) (A := k ⊗[R] AffineTangentLifts.familyAffineRing R X V)
      (S := DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X V)
      (BaseTangentTensor.baseTangentScalarReduction k R (AffineTangentLifts.familyAffineRing R X V) d)
      (familyCommonOpenProductEquiv k R X h d) (familyCommonOpenProductEquiv k R X j d)
      (familyCommonOpenProductEquiv_reduction k R X h d) (familyCommonOpenProductEquiv_reduction k R X j d) =
        CommonOpenTangentDifferences.familyCommonOpenTangentDifference k R X h j d := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  apply BaseChangedCoefficientDerivations.baseChangedCoefficientDerivation_ext R k (AffineTangentLifts.familyAffineRing R X V)
    (k ⊗[R] AffineTangentLifts.familyAffineRing R X V) (k ⊗[R] AffineTangentLifts.familyAffineRing R X V)
  intro a
  have hp : BaseTangentTensor.baseTangentScalarReduction k R (AffineTangentLifts.familyAffineRing R X V) d
      ((1 : DualNumber k) ⊗ₜ[R] a) = (1 : k) ⊗ₜ[R] a :=
    BaseTangentTensor.baseTangentScalarReduction_tmul k R (AffineTangentLifts.familyAffineRing R X V) d 1 a
  have ht := Product.ChartDifferenceCoefficients.dualProductChartDifference_coefficients (k := k)
    (A := k ⊗[R] AffineTangentLifts.familyAffineRing R X V) (P := DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X V)
    (BaseTangentTensor.baseTangentScalarReduction k R (AffineTangentLifts.familyAffineRing R X V) d)
    (familyCommonOpenProductEquiv k R X h d) (familyCommonOpenProductEquiv k R X j d)
    (familyCommonOpenProductEquiv_reduction k R X h d) (familyCommonOpenProductEquiv_reduction k R X j d)
    ((1 : DualNumber k) ⊗ₜ[R] a)
  rw [hp, familyCommonOpenProductEquiv_snd, familyCommonOpenProductEquiv_snd] at ht
  exact ht.trans (CommonOpenTangentDifferences.familyCommonOpenTangentDifference_original k R X h j d a).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenProducts

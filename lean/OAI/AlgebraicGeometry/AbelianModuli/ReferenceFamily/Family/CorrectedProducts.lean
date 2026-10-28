import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenProductNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.DerivationPresheaf
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GaugedAlgebraSquare

/-! # Corrected Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CorrectedProducts

noncomputable section

/-! Actual affine products corrected by one derivation on the
original chart. The corrections restrict to every affine subopen. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R))) [Smooth X.hom]

attribute [local irreducible] CommonOpenProducts.familyCommonOpenProductEquiv

def familyCorrectedProductEquiv {V W : X.left.affineOpens} (h : V.1 ≤ W.1)
    (d : Derivation k R k)
    (a : Derivation k (k ⊗[R] AffineTangentLifts.familyAffineRing R X W) (k ⊗[R] AffineTangentLifts.familyAffineRing R X W)) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    (DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X V) ≃ₐ[DualNumber k]
      (DualNumber k ⊗[k] (k ⊗[R] AffineTangentLifts.familyAffineRing R X V)) := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  exact ReferenceFamily.Smooth.DualChartGauges.gaugeDualProductChart (k := k) (A := k ⊗[R] AffineTangentLifts.familyAffineRing R X V)
    (S := DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X V) (CommonOpenProducts.familyCommonOpenProductEquiv k R X h d)
    (FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R k X h a)

theorem familyCorrectedProductEquiv_reduction {V W : X.left.affineOpens}
    (h : V.1 ≤ W.1) (d : Derivation k R k)
    (a : Derivation k (k ⊗[R] AffineTangentLifts.familyAffineRing R X W) (k ⊗[R] AffineTangentLifts.familyAffineRing R X W)) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    ∀ p, Dual.TensorReduction.dualTensorReduction k (k ⊗[R] AffineTangentLifts.familyAffineRing R X V)
      (familyCorrectedProductEquiv k R X h d a p) =
        BaseTangentTensor.baseTangentScalarReduction k R (AffineTangentLifts.familyAffineRing R X V) d p := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  exact ReferenceFamily.Smooth.DualChartGauges.gaugeDualProductChart_reduction (k := k) (A := k ⊗[R] AffineTangentLifts.familyAffineRing R X V)
    (S := DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X V) _ _
    (CommonOpenProducts.familyCommonOpenProductEquiv_reduction k R X h d) _

theorem familyCorrectedProductEquiv_restrict {U V W : X.left.affineOpens}
    (t : U.1 ≤ V.1) (h : V.1 ≤ W.1) (d : Derivation k R k)
    (a : Derivation k (k ⊗[R] AffineTangentLifts.familyAffineRing R X W) (k ⊗[R] AffineTangentLifts.familyAffineRing R X W)) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    (familyCorrectedProductEquiv k R X (t.trans h) d a).toAlgHom.comp
        (ProductRestrictionMaps.familyTangentTensorRestriction k R X t d) =
      (ProductRestrictionMaps.familyProductTensorRestriction k R X t).comp
        (familyCorrectedProductEquiv k R X h d a).toAlgHom := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  apply GaugedAlgebraSquare.gaugeDualProductChart_square (k := k)
    (A := k ⊗[R] AffineTangentLifts.familyAffineRing R X V) (B := k ⊗[R] AffineTangentLifts.familyAffineRing R X U)
    (P := DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X V) (Q := DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X U)
    (CommonOpenProducts.familyCommonOpenProductEquiv k R X h d)
    (CommonOpenProducts.familyCommonOpenProductEquiv k R X (t.trans h) d)
    (ProductRestrictionMaps.familyTangentTensorRestriction k R X t d) (FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R k X t)
    (FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R k X h a)
    (FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R k X (t.trans h) a)
    (CommonOpenProductNaturality.familyCommonOpenProductEquiv_restrict k R X t h d)
  intro b
  have hc := LinearMap.congr_fun (FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction_comp R k X t h) a
  change FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R k X t (FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R k X h a) =
    FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R k X (t.trans h) a at hc
  rw [← hc]
  exact (FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction_apply R k X t
    (FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R k X h a) b).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CorrectedProducts

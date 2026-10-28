import OAI.NumberTheory.PadicHodge.CrystallineAxes
import OAI.NumberTheory.PadicHodge.CrystallineDimension
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineEndAction

/-! # Crystalline Group Law -/

namespace OAI.NumberTheory.PadicHodge.CrystallineGroupLaw.FrobeniusSlope

noncomputable section

/-! A direct crystalline group-law route: actual axis maps plus a proved
product dimension bound. Operator naturality of the crystalline comparison
is not used. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductComparisonModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductEndomorphisms.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineEndAction.CM

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (q : ℕ) [Fact q.Prime]

def isoPullback {X Y : Over (Spec (.of (ZMod q)))} (e : X ≅ Y) :
    GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q Y ≃ₗ[ℚ_[q]] GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q X where
  toLinearMap := GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q e.hom
  invFun := GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q e.inv
  left_inv x := by
    have h := LinearMap.congr_fun (AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM.rationalPullback_comp q e.inv e.hom) x
    simp only [Iso.inv_hom_id, AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM.rationalPullback_id, LinearMap.comp_apply, LinearMap.id_apply] at h
    exact h
  right_inv x := by
    have h := LinearMap.congr_fun (AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM.rationalPullback_comp q e.hom e.inv) x
    simp only [Iso.hom_inv_id, AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM.rationalPullback_id, LinearMap.comp_apply, LinearMap.id_apply] at h
    exact h

variable {K : Type} [Field K] [NumberField K] {jq : K →+* ℚ_[q]}
  (A : GeometricComparison.Geometry.AbelianH1Model K q jq)
  (j : K →+* ℂ)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)

def specialProductIso : (AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductComparisonModel.CM.productModel A).specialFiber.scheme ≅
    A.specialFiber.scheme ⊗ A.specialFiber.scheme :=
  AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductEndomorphisms.CM.productBaseChange A.integral.scheme (GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q))

include j P in
theorem product_dimension_bound :
    Module.finrank ℚ_[q] (GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q (A.specialFiber.scheme ⊗ A.specialFiber.scheme)) ≤
      2 * Module.finrank ℚ_[q] A.Crystalline := by
  let B := AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductComparisonModel.CM.productModel A
  let Q := AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductComparisonModel.CM.productProjectivePresentation A j P
  have hspecial : Module.finrank ℚ_[q]
      (GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q (A.specialFiber.scheme ⊗ A.specialFiber.scheme)) =
      Module.finrank ℚ_[q] B.Crystalline := (isoPullback q (specialProductIso q A)).finrank_eq
  have hcomplex : Module.finrank ℂ (B.ComplexBetti j) =
      Module.finrank ℂ (BettiProductDimension.FrobeniusSlope.H1
        ((A.complexFiber j).scheme ⊗ (A.complexFiber j).scheme)) :=
    ((AlgebraicGeometry.Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℂ ℂ) 1).mapIso (AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductComparisonModel.CM.complexProductIso A j).op).toLinearEquiv.finrank_eq.symm
  have hbound := BettiProductDimension.FrobeniusSlope.product_finrank_le
    (AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingAdditivity.CM.complexAbelianVariety A j P)
  rw [hspecial, CrystallineDimension.FrobeniusSlope.crystalline_finrank_eq_betti B j Q, hcomplex]
  have hA := CrystallineDimension.FrobeniusSlope.crystalline_finrank_eq_betti A j P
  rw [hA]
  exact hbound

include j P in
/-- The actual crystalline degree-one group law, with no group-law or
comparison-naturality premise. -/
theorem groupLaw : AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineMonoidAction.CM.End.GroupLawIdentity q A.specialFiber.scheme := by
  let : FiniteDimensional ℚ_[q] A.Crystalline := CrystallineDimension.FrobeniusSlope.crystalline_finite A j P
  let : FiniteDimensional ℚ_[q] (AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductComparisonModel.CM.productModel A).Crystalline :=
    CrystallineDimension.FrobeniusSlope.crystalline_finite (AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductComparisonModel.CM.productModel A) j (AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductComparisonModel.CM.productProjectivePresentation A j P)
  let : FiniteDimensional ℚ_[q] (GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q (A.specialFiber.scheme ⊗ A.specialFiber.scheme)) :=
    (isoPullback q (specialProductIso q A)).symm.finiteDimensional
  exact CrystallineAxes.FrobeniusSlope.groupLaw_of_restrictions_injective q A.specialFiber.scheme
    (CrystallineAxes.FrobeniusSlope.restrictions_injective_of_dimension_bound q A.specialFiber.scheme
      (product_dimension_bound q A j P))

def crystallineRingAction : (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme)ᵐᵒᵖ →+*
    Module.End ℚ_[q] A.Crystalline := AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineEndAction.CM.ringAction q A.specialFiber.scheme (groupLaw q A j P)

theorem crystallineRingAction_frobenius :
    crystallineRingAction q A j P (MulOpposite.op
      (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme)) = A.crystallineFrobenius := rfl

end

end OAI.NumberTheory.PadicHodge.CrystallineGroupLaw.FrobeniusSlope

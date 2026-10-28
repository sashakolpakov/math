import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.SupportedProduct
import OAI.AlgebraicGeometry.CycleClass.Thom.AbsoluteProductMaps
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Degree

/-! # Product -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Integral.Product.Constructions

noncomputable section

/-! Exterior-product compatibility for the actual geometric classes of
integral supports in integral ambient varieties, with the literal projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.SupportedProduct.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProductRestriction.Constructions
  ExteriorCupForget.Constructions ExteriorImageCup.Constructions AbsoluteProductMaps.Constructions Cycle.Degree.Constructions.Class

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V W T : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (πV : T.toOver ⟶ V.toOver) (πW : T.toOver ⟶ W.toOver)
  (hprod : IsLimit (BinaryFan.mk πV πW)) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport W q)

local notation "C" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions.integralProductSupport V W T πV πW hprod p q A B

theorem integralSupportedProduct_forget :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of T.analyticSpace)
      (Set.range (C).analyticInclusion)ᶜ (2 * (p + q)) (C).rationalSupportedCycleClass =
    eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of T.analyticSpace))
      (Nat.mul_add 2 p q).symm)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (TopCat.of T.analyticSpace) (2 * p) (2 * q)
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) πV
          (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
            (Set.range A.analyticInclusion)ᶜ (2 * p) A.rationalSupportedCycleClass))
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * q) πW
          (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of W.analyticSpace)
            (Set.range B.analyticInclusion)ᶜ (2 * q) B.rationalSupportedCycleClass))) := by
  rw [← SupportedProduct.Constructions.integralSupportedProductClass_eq_cycleClass V W T πV πW hprod p q A B]
  unfold SupportedProduct.Constructions.integralSupportedProductClass
  rw [ExteriorCupForget.Constructions.relativeInclusion_pullback]
  unfold Supported.ProductRestriction.Constructions.supportedExteriorCycleClass
  rw [ExteriorCupForget.Constructions.imageExteriorCup_forget]
  exact AbsoluteProductMaps.Constructions.evenAbsoluteExteriorCup_pullback (X := TopCat.of V.analyticSpace) (Y := TopCat.of W.analyticSpace)
    (Z := TopCat.of T.analyticSpace) (SupportedProduct.Constructions.ambientProductMap V W T πV πW hprod) p q _ _

theorem integralRationalCycleClass_product : (C).rationalCycleClass =
    cast (congrArg (fun n => (T.rationalCohomology n : Type)) (add_add_add_comm p p q q))
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace T.toOver) (p + p) (q + q)
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) πV A.rationalCycleClass)
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (q + q) πW B.rationalCycleClass)) := by
  have h := integralSupportedProduct_forget V W T πV πW hprod p q A B
  rw [AbsoluteProductMaps.Constructions.absoluteDegreeCast_apply (TopCat.of T.analyticSpace) (Nat.mul_add 2 p q).symm] at h
  rw [Cycle.Degree.Constructions.Class.rationalCycleClass_as_cast (C), Cycle.Degree.Constructions.Class.rationalCycleClass_as_cast A, Cycle.Degree.Constructions.Class.rationalCycleClass_as_cast B]
  have hc := congrArg (cast (congrArg (fun n => (T.rationalCohomology n : Type)) (two_mul (p + q)))) h
  exact hc.trans (Cycle.Degree.Constructions.Class.projectionCup_degreeTransport
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map πV) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map πW)
    (two_mul p) (two_mul q) (Nat.mul_add 2 p q).symm (add_add_add_comm p p q q) (two_mul (p + q)) _ _)

theorem integralGeometricCycleClass_product : (C).geometricCycleClass =
    cast (congrArg (fun n => (T.rationalCohomology n : Type)) (add_add_add_comm p p q q))
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace T.toOver) (p + p) (q + q)
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) πV A.geometricCycleClass)
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (q + q) πW B.geometricCycleClass)) := by
  rw [← GeometricTrace.Constructions.HigherThom.rationalCycleClass_eq_geometric (C), ← GeometricTrace.Constructions.HigherThom.rationalCycleClass_eq_geometric A,
    ← GeometricTrace.Constructions.HigherThom.rationalCycleClass_eq_geometric B]
  exact integralRationalCycleClass_product V W T πV πW hprod p q A B

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Integral.Product.Constructions

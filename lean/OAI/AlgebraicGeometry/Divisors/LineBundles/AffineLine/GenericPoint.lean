import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Space
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberOpen
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberFieldNaturality

/-! # Generic Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.GenericPoint.BundleCycles

noncomputable section

/-! # LineBundleCycles: affine-line fiber generic points and rational functions on actual polynomial charts -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0})

theorem affineLineFiberGenericPoint_on_chart (U : X.affineOpens) (p : Spec Γ(X, U.1)) :
    Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) (U.2.fromSpec p) =
      Charts.BundleCycles.affineLinePolynomialChart X U (Polynomial.Projection.BundleCycles.polynomialPrimePoint Γ(X, U.1) p) := by
  exact ((congrArg (Charts.BundleCycles.affineLinePolynomialChart X U) (Polynomial.AffineSpace.BundleCycles.polynomialPrimePoint_eq_fiberGeneric Γ(X, U.1) p)).trans
    (Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_naturality (Charts.BundleCycles.affineLineProjection X) (Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1))
      U.2.fromSpec (Charts.BundleCycles.affineLinePolynomialChart X U) (Charts.BundleCycles.affineLinePolynomialChart_isPullback X U) p)).symm

variable [IsIntegral X]

theorem affineLineFunctionField_on_chart (U : X.affineOpens) [Nonempty U.1] :
    Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (Charts.BundleCycles.affineLineProjection X) ≫ RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (Charts.BundleCycles.affineLinePolynomialChart X U) =
      RationalDivisorRestriction.BundleCycles.openFunctionFieldMap U.2.fromSpec ≫ Polynomial.Projection.BundleCycles.polynomialFunctionFieldMap Γ(X, U.1) := by
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  exact (GenericFieldComposition.BundleCycles.genericFieldMap_comp (Charts.BundleCycles.affineLinePolynomialChart X U) (Charts.BundleCycles.affineLineProjection X)
    (genericPoint_eq_of_isOpenImmersion _) (Integral.FiberFieldNaturality.BundleCycles.integralFiberProjection_genericPoint (Charts.BundleCycles.affineLineProjection X))).symm.trans
      ((GenericFieldComposition.BundleCycles.genericFieldMap_congr (Charts.BundleCycles.affineLinePolynomialChart_toBase X U) _ _).trans
        (GenericFieldComposition.BundleCycles.genericFieldMap_comp (Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1)) U.2.fromSpec
          (Polynomial.Projection.BundleCycles.polynomialProjection_genericPoint Γ(X, U.1)) (genericPoint_eq_of_isOpenImmersion _)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.GenericPoint.BundleCycles

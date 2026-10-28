import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.ProductChartDifferences
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenDerivationExtension

/-! # Product Difference Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.ProductDifferenceCoefficients

noncomputable section

/-! The actual differences from a normalized global chart have
derivation coefficients. Their restriction is the constructed etale
extension on the actual affine special fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] Dual.CommonOpenFiber.dualCommonOpenFiber Dual.CommonOpenFiber.dualAffineCommonOpenFiber Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenMap
attribute [local irreducible] DualOpen.CommonTransitions.affineChartProductOnOpen Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso ProductChartDifferences.globalProductChartDifference

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k)))) [Smooth X.hom]
    (U : X.left.AffineOpenCover)
    (e : X ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection k)).obj ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)).obj X))
    (he : NormalizedDual.OpenProductData.NormalizesDualProductFiber k e)

def globalProductDifferenceCoefficient (V : X.left.affineOpens) (i : U.I₀)
    (hi : V.1 ≤ (U.f i).opensRange) :
    Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (Dual.CommonOpenFiber.dualAffineCommonOpenFiber k X V))
      (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (Dual.CommonOpenFiber.dualAffineCommonOpenFiber k X V)) :=
  AffineProduct.TransitionDerivation.affineProductTransitionDerivation k (Dual.CommonOpenFiber.dualAffineCommonOpenFiber k X V)
    (ProductChartDifferences.globalProductChartDifference k X U e he V.1 i hi)
    (ProductChartDifferences.globalProductChartDifference_reduction k X U e he V.1 i hi)

theorem globalProductDifferenceCoefficient_natural {V W : X.left.affineOpens} (h : V.1 ≤ W.1)
    (i : U.I₀) (hi : W.1 ≤ (U.f i).opensRange)
    (a : HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (Dual.CommonOpenFiber.dualAffineCommonOpenFiber k X W)) :
    Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X h (globalProductDifferenceCoefficient k X U e he W i hi a) =
      globalProductDifferenceCoefficient k X U e he V i (h.trans hi)
        (Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X h a) :=
  AffineProduct.DerivationNaturality.affineProductTransitionDerivation_natural k
    (X := Dual.CommonOpenFiber.dualAffineCommonOpenFiber k X V) (Y := Dual.CommonOpenFiber.dualAffineCommonOpenFiber k X W)
    (Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenMap k X h)
    (ProductChartDifferences.globalProductChartDifference k X U e he V.1 i (h.trans hi))
    (ProductChartDifferences.globalProductChartDifference k X U e he W.1 i hi)
    (ProductChartDifferences.globalProductChartDifference_reduction k X U e he V.1 i (h.trans hi))
    (ProductChartDifferences.globalProductChartDifference_reduction k X U e he W.1 i hi)
    (ProductChartDifferences.globalProductChartDifference_restriction k X U e he h i hi) a

theorem globalProductDifferenceCoefficient_restrict {V W : X.left.affineOpens} (h : V.1 ≤ W.1)
    (i : U.I₀) (hi : W.1 ≤ (U.f i).opensRange) :
    Dual.CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X h (globalProductDifferenceCoefficient k X U e he W i hi) =
      globalProductDifferenceCoefficient k X U e he V i (h.trans hi) := by
  apply Eq.symm
  exact EtaleHomDerivation.etaleAlgHomDerivationLinear_unique (Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X h)
    (Dual.CommonOpenDerivationExtension.dualAffineCommonOpenAlgebraMap_etale k X h)
    (globalProductDifferenceCoefficient k X U e he W i hi)
    (globalProductDifferenceCoefficient k X U e he V i (h.trans hi))
    (fun a => (globalProductDifferenceCoefficient_natural k X U e he h i hi a).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.ProductDifferenceCoefficients

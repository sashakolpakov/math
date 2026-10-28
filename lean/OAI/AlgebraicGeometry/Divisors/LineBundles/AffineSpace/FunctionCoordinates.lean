import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SpaceProperties
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CoordinateEquiv
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberFieldNaturality

/-! # Function Coordinates -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.FunctionCoordinates.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual function-field maps in affine-space coordinate decompositions -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]

theorem affineSpaceReindexEquiv_functionField {ι κ : Type} [Finite ι] [Finite κ] (e : ι ≃ κ) :
    Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineSpace ι X ↘ X) =
      Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineSpace κ X ↘ X) ≫
        RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (CoordinateEquiv.BundleCycles.affineSpaceReindexEquiv X e).hom :=
  Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap_iso (CoordinateEquiv.BundleCycles.affineSpaceReindexEquiv X e) _ _
    (CoordinateEquiv.BundleCycles.affineSpaceReindexEquiv_over X e)

theorem affineSpaceEmptyEquiv_functionField (ι : Type) [IsEmpty ι] :
    Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineSpace ι X ↘ X) =
      RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (CoordinateEquiv.BundleCycles.affineSpaceEmptyEquiv X ι).hom := rfl

theorem affineSpaceSuccEquiv_functionField (n : ℕ) :
    Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineSpace (Fin (n + 1)) X ↘ X) ≫
        RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n).inv =
      Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineSpace (Fin n) X ↘ X) ≫
        Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineLine.Charts.BundleCycles.affineLineProjection (AffineSpace (Fin n) X)) :=
  Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap_factorization (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n) _ _ _
    (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv_over X n)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.FunctionCoordinates.BundleCycles

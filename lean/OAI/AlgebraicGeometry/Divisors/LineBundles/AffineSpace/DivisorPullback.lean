import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.FunctionCoordinates
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CycleCoordinates
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IsoPrincipalDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.DivisorPullback
import Mathlib.SetTheory.Cardinal.NatCard

/-! # Divisor Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.DivisorPullback.BundleCycles

noncomputable section

/-! # LineBundleCycles: complete rational principal-divisor pullback in every finite affine-space rank -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem affineSpaceFinPrincipalDivisor_pullback (n : ℕ) (g : X.functionField) (hg : g ≠ 0) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (AffineSpace (Fin n) X)
        (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineSpace (Fin n) X ↘ X) g) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (AffineSpace (Fin n) X ↘ X) (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) := by
  induction n with
  | zero =>
    rw [FunctionCoordinates.BundleCycles.affineSpaceEmptyEquiv_functionField]
    exact (LineBundles.Scheme.IsoPrincipalDivisor.BundleCycles.schemeIsoPrincipalDivisor_pull (CoordinateEquiv.BundleCycles.affineSpaceEmptyEquiv X (Fin 0)) g).trans
      (CycleCoordinates.BundleCycles.affineSpaceEmptyEquiv_cycleExtension X (Fin 0) _)
  | succ n ih =>
    have hfield : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n).inv
        (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineSpace (Fin (n + 1)) X ↘ X) g) =
      Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineLine.Charts.BundleCycles.affineLineProjection (AffineSpace (Fin n) X))
        (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineSpace (Fin n) X ↘ X) g) :=
      ConcreteCategory.congr_hom (FunctionCoordinates.BundleCycles.affineSpaceSuccEquiv_functionField X n) g
    calc
      _ = Finsupp.mapDomain (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n).inv
          (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (AffineLine.Charts.BundleCycles.affineLine (AffineSpace (Fin n) X))
            (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n).inv
              (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineSpace (Fin (n + 1)) X ↘ X) g))) :=
        (LineBundles.Scheme.IsoPrincipalDivisor.BundleCycles.schemeIsoPrincipalDivisor_push
          (X := AffineLine.Charts.BundleCycles.affineLine (AffineSpace (Fin n) X))
          (Y := AffineSpace (Fin (n + 1)) X)
          (e := (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n).symm)
          (g := Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineSpace (Fin (n + 1)) X ↘ X) g)).symm
      _ = _ := by
        rw [hfield, AffineLine.DivisorPullback.BundleCycles.affineLinePrincipalDivisor_pullback
          (X := AffineSpace (Fin n) X)
          (g := Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineSpace (Fin n) X ↘ X) g)
          (hg := Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap_ne_zero (AffineSpace (Fin n) X ↘ X) g hg),
          ih, CycleCoordinates.BundleCycles.affineSpaceSuccEquiv_cycleExtension]

theorem affineSpacePrincipalDivisor_pullback (ι : Type) [Finite ι] (g : X.functionField) (hg : g ≠ 0) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (AffineSpace ι X)
        (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineSpace ι X ↘ X) g) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (AffineSpace ι X ↘ X) (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) := by
  let e := CoordinateEquiv.BundleCycles.affineSpaceReindexEquiv X (Finite.equivFin ι).symm
  have hfield : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap e.hom (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineSpace ι X ↘ X) g) =
      Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineSpace (Fin (Nat.card ι)) X ↘ X) g :=
    (ConcreteCategory.congr_hom (FunctionCoordinates.BundleCycles.affineSpaceReindexEquiv_functionField X (Finite.equivFin ι).symm) g).symm
  calc
    _ = Finsupp.mapDomain e.hom
        (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (AffineSpace (Fin (Nat.card ι)) X)
          (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap e.hom (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineSpace ι X ↘ X) g))) :=
      (LineBundles.Scheme.IsoPrincipalDivisor.BundleCycles.schemeIsoPrincipalDivisor_push
        (X := AffineSpace (Fin (Nat.card ι)) X)
        (Y := AffineSpace ι X)
        (e := e)
        (g := Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineSpace ι X ↘ X) g)).symm
    _ = _ := by
      rw [hfield, affineSpaceFinPrincipalDivisor_pullback X (Nat.card ι) g hg]
      exact CycleCoordinates.BundleCycles.affineSpaceReindexEquiv_cycleExtension X (Finite.equivFin ι).symm _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.DivisorPullback.BundleCycles

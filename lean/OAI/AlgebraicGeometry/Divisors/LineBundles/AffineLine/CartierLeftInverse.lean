import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ZeroDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Support
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ImageRegularFunction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierFiber

/-! # Cartier Left Inverse -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.CartierLeftInverse.BundleCycles

noncomputable section

/-! # LineBundleCycles: zero-section Cartier intersection undoes actual affine-line cycle extension -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem affineLineZeroRationalDivisor (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Charts.BundleCycles.affineLine X)
      (RegularDivisor.BundleCycles.globalFunctionFieldElement (Charts.BundleCycles.affineLine X) (Space.BundleCycles.affineLineCoordinate X)) =
        Finsupp.single (Space.BundleCycles.affineLineZeroSection X (genericPoint X)) 1 := by
  change (RegularDivisor.BundleCycles.regularFunctionDivisor (Charts.BundleCycles.affineLine X) (Space.BundleCycles.affineLineCoordinate X)).mapRange
    (fun n : ℤ => (n : ℚ)) Int.cast_zero = _
  rw [ZeroDivisor.BundleCycles.affineLineZeroDivisor_eq_single, Finsupp.mapRange_single, Int.cast_one]

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]

theorem affineLineCartierCycle_extended (W : IrreducibleCloseds X) :
    Principal.CartierCycle.BundleCycles.principalCartierPointCycle (Space.BundleCycles.affineLineCoordinate X) (Support.BundleCycles.affineLineExtendedSupport X W) =
      Finsupp.single (Space.BundleCycles.affineLineZeroSection X (irreducibleSetEquivPoints W)) 1 := by
  let A := CycleClass.Geometric.GenericPoint.reducedSupportScheme W
  let j := Support.BundleCycles.affineLineSupportMap X W
  have hc : j.appTop (Space.BundleCycles.affineLineCoordinate X) = Space.BundleCycles.affineLineCoordinate A :=
    AffineSpace.map_appTop_coord _ _
  have h := Closed.ImageRegularFunction.BundleCycles.integralClosedImage_regularDivisor j (Space.BundleCycles.affineLineCoordinate X)
  change Finsupp.mapDomain j (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Charts.BundleCycles.affineLine A)
    (RegularDivisor.BundleCycles.globalFunctionFieldElement (Charts.BundleCycles.affineLine A) (j.appTop (Space.BundleCycles.affineLineCoordinate X)))) =
      Principal.CartierCycle.BundleCycles.principalCartierPointCycle (Space.BundleCycles.affineLineCoordinate X) (Support.BundleCycles.affineLineExtendedSupport X W) at h
  rw [hc, affineLineZeroRationalDivisor, Finsupp.mapDomain_single] at h
  have hp : j (Space.BundleCycles.affineLineZeroSection A (genericPoint A)) =
      Space.BundleCycles.affineLineZeroSection X (irreducibleSetEquivPoints W) :=
    (congrArg (fun k => k (genericPoint A)) (ZeroNaturality.BundleCycles.affineLineZeroSection_naturality (CycleClass.Geometric.GenericPoint.reducedSupportι W))).trans
      (congrArg (Space.BundleCycles.affineLineZeroSection X) (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W))
  exact h.symm.trans (congrArg (fun x => Finsupp.single x (1 : ℚ)) hp)

theorem affineLineCartierCycle_extendedPoint (x : X) :
    Principal.CartierCycle.BundleCycles.principalCartierPointCycle (Space.BundleCycles.affineLineCoordinate X)
      (irreducibleSetEquivPoints.symm (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x)) =
        Finsupp.single (Space.BundleCycles.affineLineZeroSection X x) 1 := by
  have h := affineLineCartierCycle_extended X (irreducibleSetEquivPoints.symm x)
  rw [Support.BundleCycles.affineLineExtendedSupport_eq_pointClosure, irreducibleSetEquivPoints.apply_symm_apply] at h
  exact h

theorem affineLineCartierPointMap_extension (z : X →₀ ℚ) :
    Principal.CartierFiber.BundleCycles.principalCartierPointMap (Space.BundleCycles.affineLineCoordinate X) (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Charts.BundleCycles.affineLineProjection X) z) =
      Finsupp.mapDomain (Space.BundleCycles.affineLineZeroSection X) z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.mapDomain_zero]
  | add a b ha hb => simp only [map_add, ha, hb, Finsupp.mapDomain_add]
  | single x q =>
    change Principal.CartierFiber.BundleCycles.principalCartierPointMap (Space.BundleCycles.affineLineCoordinate X)
      (Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) (Finsupp.single x q)) = _
    rw [Finsupp.mapDomain_single, Principal.CartierFiber.BundleCycles.principalCartierPointMap_single, affineLineCartierCycle_extendedPoint,
      Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.mapDomain_single]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.CartierLeftInverse.BundleCycles
